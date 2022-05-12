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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "xielock",
    /* First member's full name */
    "XIE Lock",
    /* First member's email address */
    "xielock@sjtu.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define WSIZE 4
#define DSIZE 8
#define ALIGNMENT 8
#define EXTEND_SIZE (1<<12) //4KB
#define MAX(x, y)  ((x) > (y) ? (x) : (y))


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


// pack size and allocated bit into a word
#define PACK(size, alloc)  ((size) |(alloc))
// read and write a word from address p (pointer p)
#define GET(p)   (*(unsigned int *) (p))   //pointer p default type is void *, so need to change type
#define PUT(p, val)   (*(unsigned int *) (p) = (val))

//GET size and whether allocated
#define GET_SIZE(p)  (GET(p) & ~0x07)
#define GET_ALLOC(p)  (GET(p) & 0x1)

/*GET Header and footer
origin pointer point to the start of payload/ the type is char *  */
#define HDRP(bp)   ((char *)(bp) - WSIZE)
#define FTRP(bp)   ((char*)(bp) +  GET_SIZE(HDRP(bp)) - DSIZE)

//given block ptr bp , compute address of next and prvious blocks
#define NEXT_BLKP(bp)   ((char*)(bp) + GET_SIZE((char*)(bp) - WSIZE))
#define PRE_BLKP(bp)     ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE)) //GET_SIZE((char*)(bp) - DSIZE) get pre block's footer 

static char * heap_listp; //the pointer point to the begin of block's payload
static void * coalesce(void * bp);

/*extend the heap
*/
static void * extend_heap(size_t size)
{
    char * bp;
    size = ALIGN(size);
    bp = mem_sbrk(size);
    if(bp == (void*)-1)
    {
        printf("extend_heap failed mem_sbrk return -1");
        return NULL;
    }
    // beautiful !!! the new allocate block's header will overlap the pre epilogue header
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue header

    //coalesce if the previous block was free
    return coalesce(bp); 
}

/* align the block size*/
static size_t adjust_block_size(size_t size)
{
    //min_size is 16bytes
    if(size < DSIZE) // here is a new bug， < DSIZE, not 2*DSIZE, 2*DSIZE include header and footer
    size = 2* DSIZE;
    else 
    {
        //up up  add DSIZE because the header and footer
        size = (size + DSIZE + DSIZE -1) & ~(0x07);
        //size = DSIZE*(size + DSIZE + DSIZE -1) / DSIZE;
    }
    return size;
}
static void split_block(void * bp, size_t size)
{
    size_t free_size = GET_SIZE(HDRP(bp));
    if(free_size - size >= 2* DSIZE) // > 16bytes
    {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        //left of block to set zero
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(free_size - size, 0));
        PUT(FTRP(bp), PACK(free_size - size, 0));
    }
}
/* find fit */
static void * find_fit(size_t size)
{
    //every time search from the begin of the lsit
    //search ending is  01 block
    for(char* bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if(!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= size)
        {
            return bp;
        }
    }
    return NULL;
}

static void place(char * bp, size_t size)
{
    //get the free block's size
    size_t free_size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(free_size, 1));
    PUT(FTRP(bp), PACK(free_size, 1));
    split_block(bp, size);// split the block 
}

//merge the free block    4cases
static void * coalesce(void * bp)
{
    size_t pre_alloc = GET_ALLOC(HDRP(PRE_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(pre_alloc && next_alloc)  //case 1    A/A->F/A 
        return bp;
    else if(!pre_alloc && next_alloc) //case2  F/A->F/ A
    {
        //merge the pre
        char * pre = PRE_BLKP(bp);
        size_t pre_size = GET_SIZE(HDRP(pre));
        PUT(FTRP(bp), PACK(size+ pre_size, 0));
        PUT(HDRP(pre), PACK(size+ pre_size, 0));
        return pre;
    }
    else if(pre_alloc && !next_alloc) //case3  A/A->F/F
    {
        //merge to next
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size+ next_size, 0));
        PUT(FTRP(bp), PACK(size+ next_size, 0));
        return bp;
    }
    else                             //case4   F/A->F/F
    {
        char * next = NEXT_BLKP(bp);
        char * pre = PRE_BLKP(bp);
        size_t next_size = GET_SIZE(HDRP(next));
        size_t pre_size = GET_SIZE(HDRP(pre));
        PUT(HDRP(pre), PACK(pre_size+ size+ next_size, 0));
        PUT(FTRP(next), PACK(pre_size+ size+ next_size, 0));
        return pre;
    }

}
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    heap_listp = mem_sbrk(4* WSIZE); //allocate 4个字节
    if(heap_listp == (void*)-1)  //((void *)-1) transfer -1 to pointer xFFFFFFFF
        return -1;                  //in this case sys doesn't have enough space
    PUT(heap_listp, 0); //aligment padding 
    PUT(heap_listp + (1* WSIZE), PACK(DSIZE, 1));// prologue header
    PUT(heap_listp + (2* WSIZE), PACK(DSIZE, 1));// prologue footer
    PUT(heap_listp + (3* WSIZE), PACK(0, 1)); // end block
    heap_listp += 2*WSIZE;
    //extend heap finish the extend of the free block
    if(extend_heap(EXTEND_SIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    if(size == 0)return NULL;// ignore zero
    size = adjust_block_size(size);
    char * bp;
    size_t extend_size; //extend size if can't find block
    if((bp = find_fit(size)) == NULL)
    {
        extend_size = MAX(size, EXTEND_SIZE); //4KB is max
        if((bp = extend_heap(extend_size) )== NULL)  // jesus forget to add () for expression bp = extend_headp(extend_size), bug for a long time
        {
            return NULL;
        }
    }
    place(bp, size);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);//merge 
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    if(size == 0)
    {
        mm_free(ptr);
        return NULL;
    }    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    size_t copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
 













