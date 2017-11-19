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
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE ((1 << 12)) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define LENLIST 16

#define PAR(p) *(void**)p
#define CHA(p) *(void**)(CHA_PT(p))
#define PAR_PT(p) (void*)p
#define CHA_PT(p) ((void*)p + WSIZE)
#define PUT_PT(p, ptr) *(void**)p = ptr;

void **seg_list;
void *heap_listp;

static void insert_node (void *bp, size_t size){
	int asize = size;
	int i = 0;
	for (i = 0; i < LENLIST; i++) {
		if (asize <= 1 || i == LENLIST - 1) break;
		asize >>= 1;
	}
	void* p = seg_list[i];
	void *insp = NULL;

	PUT_PT(PAR_PT(bp), p);
	if (p != NULL)
		PUT_PT(CHA_PT(p), bp);

	PUT_PT(CHA_PT(bp), insp);
	if (insp != NULL) {
		PUT_PT(PAR_PT(insp), bp);
	} else {
		seg_list[i] = bp;
	}
}



static void delete_node (void *bp){
	int i = 0;
	int size = GET_SIZE(HDRP(bp));


	for (i = 0; i < LENLIST; i++) {
		if (size <= 1 || i == LENLIST - 1)
			break;
		size >>= 1;
	}

	if (PAR(bp) != NULL)
		PUT_PT(CHA_PT(PAR(bp)), CHA(bp));

	if (CHA(bp) != NULL)
		PUT_PT(PAR_PT(CHA(bp)), PAR(bp));

	if (CHA(bp) == NULL)
		seg_list[i] = PAR(bp);
}


static void *coalesce (void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));


	if (prev_alloc && next_alloc) { /* Case 1 */
		return bp;
	}

	else if (prev_alloc && !next_alloc) { /* Case 2 */
		delete_node(bp);
		delete_node(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc) { /* Case 3 */
		delete_node(bp);
		delete_node(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	else { /* Case 4 */
		delete_node(bp);
		delete_node(PREV_BLKP(bp));
		delete_node(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
		        GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	insert_node(bp, size);

	return bp;
}

static void *place (void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));

	delete_node(bp);

	if ((csize - asize) > (2 * DSIZE)) {
		size_t remainder = csize - asize;
		if (asize >= 112) {
			//for case 7,8
			PUT(HDRP(bp), PACK(remainder, 0));
			PUT(FTRP(bp), PACK(remainder, 0));
			//bp = NEXT_BLKP(bp);
			PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
			PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
			insert_node(bp, remainder);
			return NEXT_BLKP(bp);
		}

		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		//bp = NEXT_BLKP(bp);
		PUT(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0));
		insert_node(NEXT_BLKP(bp), remainder);
	}
	else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}

	return bp;
}

static void *extend_heap (size_t words)
{
	char *bp;
	size_t size;

/* Allocate an even number of words to maintain alignment */
	size = ALIGN(words);

	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;

/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	insert_node(bp, size);

/* Coalesce if the previous block was free */
	return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init (void)
{
	//void* heap_listp;
	int i;


	//allocate memory for segregated list
	seg_list = mem_sbrk(sizeof(void*) * LENLIST);
	for (i = 0; i < LENLIST; i++) {
		seg_list[i] = NULL;
	}


	//set initial heap size
	if ((long)(heap_listp = mem_sbrk(2 * DSIZE)) == -1)
		return -1;

	PUT(heap_listp, 0); /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */
	heap_listp += (2 * WSIZE);

/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(64) == NULL)
		return -1;
	return 0;
}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc (size_t size)
{
	size_t asize; /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	char *bp;

/* Ignore spurious requests */
	if (size == 0)
		return NULL;

/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = ALIGN(size + DSIZE);

	int i = 0;
	size_t ssize = asize;
	for (i = 0; i < LENLIST; i++) {
		if ((i == LENLIST - 1) || ((ssize <= 1) && (seg_list[i] != NULL))) {
			bp = seg_list[i];
			while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))) {
				bp = PAR(bp);
			}
			//proper size not found
			if (bp != NULL)
				break;
		}
		ssize >>= 1;
	}

	if (bp != NULL) {
		bp = place(bp, asize);
		return bp;
	}

/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize)) == NULL)
		return NULL;
	bp = place(bp, asize);

	return bp;

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free (void *ptr)
{
	size_t size = GET_SIZE(HDRP(ptr));

	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	insert_node(ptr, size);
	coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc (void *ptr, size_t size)
{

	void *newptr;
	size_t copysize;
	size_t extendsize;
	int buffsize;

	if (size == 0) {
		mm_free(ptr);
		return NULL;
	}

	if (size <= DSIZE) {
		copysize = 2 * DSIZE;
	} else
		copysize = ALIGN(size + DSIZE);

	buffsize = GET_SIZE(HDRP(ptr)) - copysize;

	if (ptr == NULL) {
		return mm_malloc(size);
	}

	if (buffsize >= 0) {
		return ptr;
	} else {
		void* prev_ptr = PREV_BLKP(ptr);
		if (!GET_ALLOC(HDRP(prev_ptr))) {
			int remainder = buffsize + GET_SIZE(HDRP(prev_ptr));
			if (remainder >= 0) {
				delete_node(prev_ptr);
				PUT(HDRP(prev_ptr), PACK(copysize + remainder, 1));
				PUT(FTRP(prev_ptr), PACK(copysize + remainder, 1));
				memcpy(prev_ptr, ptr, copysize);
				return prev_ptr;
			}
		}
		void* next_ptr = NEXT_BLKP(ptr);
		if (!GET_ALLOC(HDRP(next_ptr))) {
			int remainder = buffsize + GET_SIZE(HDRP(next_ptr));
			if (remainder >= 0) {
				delete_node(next_ptr);
				PUT(HDRP(ptr), PACK(copysize + remainder, 1));
				PUT(FTRP(ptr), PACK(copysize + remainder, 1));
				return ptr;
			} else {
				extendsize = MAX(-remainder, CHUNKSIZE);
				if (extend_heap(extendsize) == NULL)
					return NULL;
				remainder += extendsize;
				delete_node(next_ptr);
				PUT(HDRP(ptr), PACK(copysize + remainder, 1));
				PUT(FTRP(ptr), PACK(copysize + remainder, 1));
				return ptr;
			}
		}
		newptr = mm_malloc(size);
		size_t oldsize;
		oldsize = GET_SIZE(HDRP(ptr));
		if (size < oldsize) oldsize = size;
		memcpy(newptr, ptr, oldsize);
		mm_free(ptr);
		return newptr;
	}
}
