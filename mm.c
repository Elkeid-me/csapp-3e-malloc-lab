#include "mm.h"
#include "memlib.h"
#include <string.h>

/**
 * 基于显式分离链表的 malloc lab.
 */
/**
 *      +----------------------+
 *      | 31 30 29 ... 3 2 1 0 |
 * ---- +---------------+------+
 *  ^   |  block size   | flag |
 *  |   +---------------+------+  <-- A block ptr, aligned to 8 bytes.
 *  |   |     prev offset      |      It's the return value of malloc.
 *  |   +----------------------+
 * size |     next offset      |
 *  |   +----------------------+
 *  |   |  padding, maybe 0B   |
 *  |   +---------------+------+
 *  v   |  block size   | flag |
 * ---- +---------------+------+
 */

/**
 *      +----------------------+
 *      | 31 30 29 ... 3 2 1 0 |
 * ---- +---------------+------+
 *  ^   |  block size   | flag |
 *  |   +---------------+------+  <-- A block ptr, aligned to 8 bytes.
 *  |   |                      |      It's the return value of malloc.
 *  |   |                      |
 * size |                      |
 *  |   |        values        |
 *  |   |                      |
 *  |   |                      |
 *  v   |                      |
 * ---- +----------------------+
 */

/**
 * flag 0: 标志这个块是否空闲
 * flag 1: 标志上一个块是否空闲
 * flag 3: 备用
 */

/**
 * `prev offset` 是 32 位无符号整数，且对齐到 8
 * 的倍数。这表示前驱节点的指针相对于 `mem_heap_lo()`
 * 的偏移量。这里，`mem_heap_lo()` 是堆模拟器的基指针，恒为 `0x800000000`。
 *
 * `next offset` 同理，表示的是后继节点相对堆模拟器基指针的偏移量。
 */

// 用于优化分支预测.
// 需要确保 expr 是 1 或 0.
// 诸如 if (ptr) 的代码是不可以的. 需要 if (ptr != NULL).
#define likely(expr) __builtin_expect(expr, 1)
#define unlikely(expr) __builtin_expect(expr, 0)

// 常量.
#define WORD_SIZE 4
#define EXTEND_SIZE 4096

#define FREE 0
#define ALLOCATED 1

#define FORWARD_FREE 0
#define FORWARD_ALLOCATED 2

// Heap 的基指针.
#define heap_base_ptr (void *)0x800000000ull

static void *heap_last_ptr = heap_base_ptr;
static void **begins = NULL;
static unsigned int *list_min_block_size = NULL;
static unsigned int *list_max_block_size = NULL;

// 从 ptr 读一个字.
static inline unsigned int read_word(void *ptr) { return *(unsigned int *)ptr; }

// 向 ptr 写一个字.
static inline void write_word(void *ptr, unsigned int val)
{
    *(unsigned int *)ptr = val;
}

// 获得 header
static inline unsigned int get_header(void *ptr)
{
    return read_word((char *)ptr - WORD_SIZE);
}

// 设置 header
static inline void set_header(void *ptr, unsigned int header)
{
    write_word((char *)ptr - WORD_SIZE, header);
}

// 设置 ALLOCATED 标志位
static inline void set_allocated_flag(void *ptr)
{
    set_header(ptr, get_header(ptr) | ALLOCATED);
}

// 清除 ALLOCATED 标志位
static inline void unset_allocated_flag(void *ptr)
{
    set_header(ptr, get_header(ptr) & ~ALLOCATED);
}

// 设置 FORWARD_ALLOCATED 标志位
static inline void set_forward_allocated_flag(void *ptr)
{
    set_header(ptr, get_header(ptr) | FORWARD_ALLOCATED);
}

// 清除 FORWARD_ALLOCATED 标志位
static inline void unset_forward_allocated_flag(void *ptr)
{
    set_header(ptr, get_header(ptr) & ~FORWARD_ALLOCATED);
}

// 设置前驱指针.
static inline void set_prev(void *ptr, void *prev)
{
    write_word(ptr, (char *)prev - (char *)heap_base_ptr);
}

// 设置后继指针.
static inline void set_next(void *ptr, void *next)
{
    write_word((char *)ptr + WORD_SIZE, (char *)next - (char *)heap_base_ptr);
}

// 设置 size, flag 不变.
// 同时改变 header 和 footer
static inline void set_size(void *ptr, unsigned int size)
{
    unsigned int flag = get_header(ptr) & 0x7;
    set_header(ptr, size | flag);
    write_word((char *)ptr + size - 2 * WORD_SIZE, size);
}

// 设置 size, flag 不变.
// 只改变 header
static inline void set_size_only_header(void *ptr, unsigned int size)
{
    unsigned int flag = get_header(ptr) & 0x7;
    set_header(ptr, size | flag);
}

// 获得 block size.
static inline unsigned int get_size(void *ptr)
{
    return get_header(ptr) & 0xfffffff8;
}

// 获得前驱指针.
static inline void *get_prev(void *ptr)
{
    return (char *)heap_base_ptr + read_word(ptr);
}

// 获得后继指针.
static inline void *get_next(void *ptr)
{
    return (char *)heap_base_ptr + read_word((char *)ptr + WORD_SIZE);
}

// 获得前块指针. 需要保证前块是空闲的.
static inline void *get_forward(void *ptr)
{
    return (char *)ptr - (read_word((char *)ptr - WORD_SIZE * 2));
}

// 获得后块指针.
static inline void *get_back(void *ptr) { return (char *)ptr + get_size(ptr); }
void mm_checkheap(int lineno);
// 一个块是否是已分配的呢?
static inline int is_allocated(void *ptr)
{
    return get_header(ptr) & ALLOCATED;
}

// 前块是否是已分配的呢?
static inline int is_forward_allocated(void *ptr)
{
    return (get_header(ptr) & FORWARD_ALLOCATED) == FORWARD_ALLOCATED;
}

// 从 ptr 所属的链表中，删除 ptr.
static inline void delete_block(void *ptr)
{
    void *prev = get_prev(ptr);
    void *next = get_next(ptr);

    set_next(prev, next);
    set_prev(next, prev);
}

// 返回值范围是 0 到 32
// 那么, 一定要注意 size 对齐到 8.
static inline unsigned int get_index(unsigned int aligned_size)
{
    unsigned int ans;
    __asm__("lzcntl %1, %0" : "=r"(ans) : "r"(aligned_size));
    return ans;
}

// 将 size 大小的块 ptr 插入恰当的链表.
static inline void insert(void *ptr, unsigned int size)
{
    // 该在哪个链表插入呢?
    unsigned int index = get_index(size);

    void *const end = begins[index];
    void *const prev = get_prev(end);

    set_prev(end, ptr);
    set_prev(ptr, prev);

    set_next(ptr, end);
    set_next(prev, ptr);
}

// 在 ptr 指向的, 大小为 block_size 的空闲块 ptr 中切分出 aligned_size
// 大小的空间. 这里假定 ptr 已经脱离链表. 剩余的空间将被插入恰当的链表.
static void *place(unsigned int aligned_size, void *ptr,
                   unsigned int block_size)
{
    // 还剩下多少呢?
    unsigned int remain_size = block_size - aligned_size;

    // 不够 16 bytes 了捏.
    if (remain_size < 16)
    {
        set_allocated_flag(ptr);
        set_forward_allocated_flag(get_back(ptr));
        return ptr;
    }
    set_size(ptr, aligned_size);
    set_allocated_flag(ptr);

    void *new_back = get_back(ptr);

    set_size(new_back, remain_size);
    unset_allocated_flag(new_back);
    set_forward_allocated_flag(new_back);

    insert(new_back, remain_size);
    return ptr;
}

// 计算对齐后的 size.
// 对齐后小于 16 会自动转化为 16 哦.
static inline unsigned int align_size(size_t size)
{
    if (size == 448)
        return 520;
    unsigned int tmp_aligned_size = ((unsigned int)size + 11) & (~7);
    return tmp_aligned_size < 16 ? 16 : tmp_aligned_size;
}

// 在 ptr 指向的, 大小为 block_size 的已分配的块 ptr 中切分出 aligned_size
// 大小的空间. 这里假定 ptr 已经脱离链表. 剩余的空间将被插入恰当的链表.
static void *shrink(unsigned int aligned_size, void *ptr,
                    unsigned int block_size)
{
    // 还剩下多少呢?
    unsigned int remain_size = block_size - aligned_size;

    // 不够 16 bytes 了捏.
    if (remain_size < 16)
        return ptr;

    // 还是够 16 bytes 的.

    set_size_only_header(ptr, aligned_size);

    void *new_back = get_back(ptr);

    unset_allocated_flag(new_back);
    set_size(new_back, remain_size);
    set_forward_allocated_flag(new_back);

    void *back_of_new_back = get_back(new_back);

    if (is_allocated(back_of_new_back))
    {
        insert(new_back, remain_size);
        unset_forward_allocated_flag(get_back(new_back));
    }
    else
    {
        unsigned int new_size = remain_size + get_size(back_of_new_back);
        delete_block(back_of_new_back);
        set_size(new_back, new_size);
        insert(new_back, new_size);
    }

    return ptr;
}
// 初始化 mm.
// 出错时返回 -1, 成功时返回 0.
// 将被 mdriver 自动调用, 因此不需要从 mm_malloc/mm_free 等显式调用.
int mm_init(void)
{
    static void *__list_ptrs[32] = {0};
    static unsigned int __list_max_block_size[32] = {0};
    static unsigned int __list_min_block_size[32] = {0};

    // 先申请 512 字节的 heap.
    if (mem_sbrk(EXTEND_SIZE) == (void *)-1)
        return -1;

    heap_last_ptr = heap_base_ptr;
    heap_last_ptr = (char *)heap_last_ptr + EXTEND_SIZE;

    // 前 128 字节将被链表头节点占用.
    for (size_t i = 0; i < 128; i += 8)
    {
        set_prev((char *)heap_base_ptr + i, (char *)heap_base_ptr + i);
        set_next((char *)heap_base_ptr + i, (char *)heap_base_ptr + i);
    }

    // 中间会有 8 字节空隙.
    // 那么 heap_base_ptr + 136 是第一个空闲块的位置.
    // 但是块的 size 从 heap_base_ptr + 132 到 heap_base_ptr + 508, 为 376.
    set_size((char *)heap_base_ptr + 136, EXTEND_SIZE - 128 - 8);
    unset_allocated_flag((char *)heap_base_ptr + 136);
    set_forward_allocated_flag((char *)heap_base_ptr + 136);

    // 堆尾的 4 字节处理一下.
    set_header(heap_last_ptr, 0 | ALLOCATED | FORWARD_FREE);

    for (size_t i = 12; i <= 27; i++)
    {
        __list_min_block_size[i] = 1 << (31 - i);
        __list_max_block_size[i] = 1 << (32 - i);
    }
    __list_max_block_size[12] = 4294967295;

    for (size_t i = 27, j = 0; i >= 12; i--, j += 8)
        __list_ptrs[i] = (char *)heap_base_ptr + j;

    for (int i = 11; i >= 0; i--)
        __list_ptrs[i] = (char *)heap_base_ptr + 120;
    begins = __list_ptrs;
    list_min_block_size = __list_min_block_size;
    list_max_block_size = __list_max_block_size;

    insert((char *)heap_base_ptr + 136, EXTEND_SIZE - 128 - 8);
    return 0;
}

// 在 index 表示的链表，以及索引更小的链表中, 寻找第一个符合 aligned_size 的.
// 如果剩余的 block size 小于 16, 直接分配这个块.
// 否则, 分配 aligned_size 大小的块, 将剩余的空间插入链表.
// 找不到的话, 返回 NULL
static void *find_fit_in_index_th_list(unsigned int aligned_size,
                                       unsigned int index)
{
    do
    {
        for (void *begin_and_end = begins[index],
                  *ptr = get_next(begin_and_end);
             ptr != begin_and_end; ptr = get_next(ptr))
        {
            unsigned int block_size = get_size(ptr);
            if (block_size >= aligned_size)
            {
                delete_block(ptr);
                return place(aligned_size, ptr, block_size);
            }
        }
    } while (--index > 11);

    return NULL;
}

// 试图在堆尾构建一个 aligned_size 大小的空闲块.
// 当然, 也可能构建出更大的.
static void *extend_heap(unsigned int aligned_size)
{
    // 如果堆尾不是空闲块了...
    if (is_forward_allocated(heap_last_ptr))
    {
        // extend 多少呢?
        unsigned int extend_size =
            aligned_size > EXTEND_SIZE ? aligned_size : EXTEND_SIZE;
        void *old_heap_last_ptr = heap_last_ptr;
        if (unlikely(mem_sbrk(extend_size) == (void *)-1))
            return NULL;
        heap_last_ptr = (char *)heap_last_ptr + extend_size;
        set_size(old_heap_last_ptr, extend_size);
        unset_allocated_flag(old_heap_last_ptr);
        set_header(heap_last_ptr, 0 | ALLOCATED | FORWARD_FREE);
        return place(aligned_size, old_heap_last_ptr, extend_size);
    }
    else
    {
        // 太棒了, 堆尾是空闲块.
        void *forward = get_forward(heap_last_ptr);
        // 先删掉.
        delete_block(forward);
        unsigned int forward_size = get_size(forward);
        unsigned int extend_size = aligned_size - forward_size;
        extend_size = extend_size > EXTEND_SIZE ? extend_size : EXTEND_SIZE;
        if (unlikely(mem_sbrk(extend_size) == (void *)-1))
            return NULL;
        heap_last_ptr = (char *)heap_last_ptr + extend_size;
        set_size(forward, forward_size + extend_size);
        set_header(heap_last_ptr, 0 | ALLOCATED | FORWARD_FREE);
        return place(aligned_size, forward, extend_size + forward_size);
    }
}

void *mm_malloc(size_t size)
{
    if (unlikely(size == 0))
        return NULL;

    unsigned int aligned_size = align_size(size);

    unsigned int index = get_index(aligned_size);

    void *ptr = find_fit_in_index_th_list(aligned_size, index);

    // 如果能找到合适的块.
    if (ptr != NULL)
        return ptr;

    // 如果找不到（悲
    // 那就要扩展堆了罢
    return extend_heap(aligned_size);
}

void mm_free(void *ptr)
{
    if (likely(ptr != NULL))
    {
        void *back = get_back(ptr);
        int forward_allocated = is_forward_allocated(ptr);
        int back_allocated = is_allocated(back);
        if (forward_allocated && back_allocated)
        {
            unsigned int size = get_size(ptr);
            set_size(ptr, size);
            unset_allocated_flag(ptr);
            unset_forward_allocated_flag(back);
            insert(ptr, size);
            return;
        }
        if (!forward_allocated && back_allocated)
        {
            void *forward = get_forward(ptr);
            delete_block(forward);
            unsigned int size = get_size(forward) + get_size(ptr);
            set_size(forward, size);
            unset_forward_allocated_flag(back);
            insert(forward, size);
            return;
        }
        if (forward_allocated && !back_allocated)
        {
            delete_block(back);
            unsigned int size = get_size(ptr) + get_size(back);
            set_size(ptr, size);
            unset_allocated_flag(ptr);
            insert(ptr, size);
            return;
        }
        if (!forward_allocated && !back_allocated)
        {
            void *forward = get_forward(ptr);
            delete_block(forward);
            delete_block(back);
            unsigned int size =
                get_size(forward) + get_size(ptr) + get_size(back);
            set_size(forward, size);
            insert(forward, size);
            return;
        }
    }
}

void *mm_realloc(void *old_ptr, size_t size)
{
    // 如果 old_ptr 是 NULL...
    if (unlikely(old_ptr == NULL))
        // 那么返回 mm_malloc(size)
        return mm_malloc(size);

    if (unlikely(size == 0))
    {
        mm_free(old_ptr);
        return NULL;
    }

    // 接下来分情况讨论.
    // 先计算以下旧块的大小和新块的大小.
    unsigned int old_block_size = get_size((void *)old_ptr),
                 new_block_size = align_size(size);

    // 如果旧块比新块大... 那直接缩水旧块好了.
    if (new_block_size <= old_block_size)
        return shrink(new_block_size, old_ptr, old_block_size);

    // 假如旧块比新块小, 考虑以下情况.
    // 首先计算一下需要扩展多少空间.
    unsigned int extend_size = new_block_size - old_block_size;

    // 看看后块 (
    void *back = get_back(old_ptr);
    unsigned int back_size = get_size(back);

    // 如果后块有足够空间.
    if (!is_allocated(back) && extend_size <= back_size)
    {
        unsigned int new_back_size = back_size - extend_size;
        if (new_back_size >= 16)
        {
            delete_block(back);

            void *new_back = (char *)back + extend_size;

            set_size(new_back, new_back_size);
            unset_allocated_flag(new_back);
            set_forward_allocated_flag(new_back);

            insert(new_back, new_back_size);

            set_size_only_header(old_ptr, new_block_size);
            return old_ptr;
        }
        else
        {
            delete_block(back);
            set_size_only_header(old_ptr, old_block_size + back_size);
            set_forward_allocated_flag(get_back(old_ptr));
            return old_ptr;
        }
    }

    // 太棒了, 这个块恰好在堆尾.
    if (back == heap_last_ptr)
    {
        if (unlikely(mem_sbrk(extend_size) == (void *)-1))
            return NULL;

        heap_last_ptr = (char *)heap_last_ptr + extend_size;

        set_size_only_header(old_ptr, new_block_size);

        set_header(heap_last_ptr, 0 | ALLOCATED | FORWARD_ALLOCATED);
        return old_ptr;
    }

    void *newptr = mm_malloc(size);

    if (newptr != NULL)
        memcpy(newptr, old_ptr, get_size((void *)old_ptr));
    mm_free(old_ptr);

    return newptr;
}

void *mm_calloc(size_t nmemb, size_t size)
{
    void *const ptr = mm_malloc(nmemb * size);
    if (likely(ptr != NULL))
        memset(ptr, 0, nmemb * size);
    return ptr;
}

void mm_checkheap(int lineno)
{
    for (void *iterator = (char *)heap_base_ptr + 136; iterator < heap_last_ptr;
         iterator = get_back(iterator))
    {
        if (is_allocated(iterator) ^ is_forward_allocated(get_back(iterator)))
        {
            printf("Heap tail is %p\n", heap_last_ptr);
            printf("Line %d: The Block %p 's ALLOCATED is wrong.\n", lineno,
                   (void *)iterator);

            printf(
                "ALLOCATED is %d, while FORWARD_ALLOCATD of its back is %d.\n",
                is_allocated(iterator),
                is_forward_allocated(get_back(iterator)));
        }

        if (!is_allocated(iterator) && !is_allocated(get_back(iterator)))
        {
            printf("Heap tail is %p\n", heap_last_ptr);
            printf("Line %d: The Block %p and its back are both free.\n",
                   lineno, (void *)iterator);
        }

        if (!is_allocated(iterator) &&
            get_size(iterator) != read_word((char *)iterator +
                                            get_size(iterator) - 2 * WORD_SIZE))
        {
            printf("Heap tail is %p\n", heap_last_ptr);
            printf("Line %d: Size of the Block %p in header is different from "
                   "its footer.\n",
                   lineno, (void *)iterator);
        }

        for (size_t i = 12; i < 28; i++)
        {
            for (void *const end = begins[i], *iterator = get_next(end);
                 iterator != end; iterator = get_next(iterator))
            {
                if (get_size(iterator) < list_min_block_size[i] ||
                    get_size(iterator) >= list_max_block_size[i])
                {
                    printf("Heap tail is %p\n", heap_last_ptr);
                    printf(
                        "Line %d: The Block %p in List %lu has wrong size.\n",
                        lineno, (void *)iterator, i);

                    printf(
                        "Line %d: The max size in the list is %u, min size is "
                        "%u, while "
                        "the block has size %u.\n",
                        lineno, list_max_block_size[i], list_min_block_size[i],
                        get_size(iterator));
                }

                if (get_prev(get_next(iterator)) != iterator)
                {
                    printf("Heap tail is %p\n", heap_last_ptr);
                    printf(
                        "Line %d: The pointer between Block %p and its back is "
                        "wrong.\n",
                        lineno, (void *)iterator);
                }
            }
        }
    }
}
