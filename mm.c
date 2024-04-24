/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

team_t team = {
    "20210669",
    "Hoseok Lee",
    "hslee0608@postech.ac.kr",
    "",
    ""
};

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define SIZECLASSNUM 20

/*defining macros*/
#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x): (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (int)(val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)bp - WSIZE)
#define FTRP(bp) ((char *)bp + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define PRED(bp) ((char *)(bp))
#define SUCC(bp) ((char *)(bp) + DSIZE)
#define SUCC_BLKP(bp) (*(char **)SUCC(bp))
#define PRED_BLKP(bp) (*(char **)PRED(bp))

/*function declarations*/
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void insert_block(void* bp);
static void delete_block(void* bp);

static char* heap_listp;
static char* seg_list[SIZECLASSNUM];
static int reall = 0;
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(DSIZE, 1));
    heap_listp += 2 * WSIZE;
    
    int i;
    for(i=0; i < SIZECLASSNUM; i++)
        seg_list[i] = NULL;

    if(extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size==0)
        return NULL;
    if(size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size){
    if(size == 0 && ptr != NULL){
        mm_free(ptr);
        return NULL;
    }
    if(ptr == NULL)
        return mm_malloc(size);

    size_t copysize = GET_SIZE(HDRP(ptr));
    size_t asize = MAX(ALIGN(size + DSIZE), 3 * DSIZE);
    if(asize <= copysize)
        return ptr;
    reall = 1;
    void *newptr = mm_malloc(size);
    if(newptr == NULL)
        return NULL;
    memcpy(newptr, ptr, copysize);
    mm_free(ptr);
    reall = 0;
    return newptr;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
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

    if(prev_alloc && next_alloc)
        ;
    else if(prev_alloc && !next_alloc){
        delete_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){
        delete_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        delete_block(NEXT_BLKP(bp));
        delete_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_block(bp);
    return bp;
}   

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    delete_block(bp);

    if((!reall) && ((csize - asize) >= (3 * DSIZE))){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        insert_block(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    return;
}

static void *find_fit(size_t asize){
    void *bp;
    int seg_index = 0;
    size_t size = asize / WSIZE;

    while((seg_index < SIZECLASSNUM - 1) && (size >= WSIZE)){
        seg_index++;
        size >>= 1;;
    }
    
    int i;
    for (i = seg_index; i < SIZECLASSNUM; i++) {
        for (bp = seg_list[i]; bp != NULL; bp = PRED_BLKP(bp)) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
        }
    }

    return NULL;
}

static void insert_block(void* bp){
    int seg_index = 0;
    size_t size = GET_SIZE(HDRP(bp)) / WSIZE;

    while((seg_index < SIZECLASSNUM - 1) && (size >= WSIZE)){
        seg_index++;
        size >>= 1;;
    }

    if (seg_list[seg_index] == NULL) {
        seg_list[seg_index] = bp;
        PUT(SUCC(bp), NULL);
        PUT(PRED(bp), NULL);
        return;
    }

    PUT(PRED(bp), seg_list[seg_index]);
    PUT(SUCC(bp), NULL);
    PUT(SUCC(seg_list[seg_index]), bp);
    seg_list[seg_index] = bp;
    return;
}

static void delete_block(void* bp) {
    int seg_index = 0;
    size_t size = GET_SIZE(HDRP(bp)) / WSIZE;

    while((seg_index < SIZECLASSNUM - 1) && (size >= WSIZE)){
        seg_index++;
        size >>= 1;;
    }

    if((PRED_BLKP(bp) == NULL) && (SUCC_BLKP(bp) == NULL))
        seg_list[seg_index] = PRED_BLKP(bp);
    else if(PRED_BLKP(bp) == NULL)
        PUT(PRED(SUCC_BLKP(bp)), PRED_BLKP(bp));
    else if(SUCC_BLKP(bp) == NULL){
        PUT(SUCC(PRED_BLKP(bp)), SUCC_BLKP(bp));
        seg_list[seg_index] = PRED_BLKP(bp);
    }
    else{
        PUT(SUCC(PRED_BLKP(bp)), SUCC_BLKP(bp));
        PUT(PRED(SUCC_BLKP(bp)), PRED_BLKP(bp));
    }
    return;
}






