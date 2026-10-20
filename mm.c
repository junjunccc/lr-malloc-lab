#include "mm.h"
#include "memlib.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define MINBLOCK (2 * DSIZE)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))
static char *heap_listp = NULL;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static size_t adjust(size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void absorb(char *ptr, char *next, size_t asize);
int mm_init(void) {
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}
void *mm_malloc(size_t size) {
    size_t extendsize;
    size_t asize;
    char *bp;
    if (size == 0)
        return NULL;
    asize = adjust(size);
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}
void mm_free(void *ptr) {
    size_t size;
    if (ptr == NULL)
        return;
    size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}
void *mm_realloc(void *ptr, size_t size) {
    size_t oldsize;
    size_t asize;
    size_t need;
    size_t copysize;
    char *next;
    void *newptr;
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    oldsize = GET_SIZE(HDRP(ptr));
    asize = adjust(size);
    if (asize <= oldsize) {
        if (oldsize - asize >= MINBLOCK) {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            char *rest = NEXT_BLKP(ptr);
            PUT(HDRP(rest), PACK(oldsize - asize, 0));
            PUT(FTRP(rest), PACK(oldsize - asize, 0));
            coalesce(ptr);
        }
        return ptr;
    }
    next = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next)) && oldsize + GET_SIZE(HDRP(next)) >= asize) {
        absorb(ptr, next, asize);
        return ptr;
    }
    if (GET_SIZE(HDRP(next)) == 0) {
        need = asize - oldsize;
        if (extend_heap(need / WSIZE) != NULL) {
            absorb(ptr, next, asize);
            return ptr;
        }
    }
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copysize = oldsize - DSIZE;
    if (size < copysize)
        copysize = size;
    memcpy(newptr, ptr, copysize);
    mm_free(ptr);
    return newptr;
}
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk((int)size)) == (void *)-1)
        return NULL;
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {
        return bp;
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}
static size_t adjust(size_t size) {
    if (size <= DSIZE)
        return MINBLOCK;
    return DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
}
static void *find_fit(size_t asize) {
    char *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    return NULL;
}
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= MINBLOCK) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
static void absorb(char *ptr, char *next, size_t asize) {
    size_t oldsize = GET_SIZE(HDRP(ptr));
    size_t combined = oldsize + GET_SIZE(HDRP(next));
    char *rest;
    if (combined - asize >= MINBLOCK) {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        rest = NEXT_BLKP(ptr);
        PUT(HDRP(rest), PACK(combined - asize, 0));
        PUT(FTRP(rest), PACK(combined - asize, 0));
        coalesce(rest);
    } else {
        PUT(HDRP(ptr), PACK(combined, 1));
        PUT(FTRP(ptr), PACK(combined, 1));
    }
}