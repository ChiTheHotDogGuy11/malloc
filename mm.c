
/*
 * mm.c
 *
 * Justin Greet, jgreet
 *
 * I used an explicit free list (ordered by address) and 
 * used a combination of best fit/ first fit. The prologue
 * points to the first member of the list, and the last member
 * points to the epilogue. Each free cell is structured like
 * |Header|previous block offset|next block offset|. I have no
 * footers and am using offsets instead of pointers to save space.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUGn
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/**********************************
 ** GLOBAL VARIABLES
**********************************/
//Pointer that always points to prologue head.
static char *prologue_headp = 0;
//Pointer that always points to epilogue head.
static char *epilogue_headp = 0;
//Points to the epilogue_headp, so that I can update the
//freeList pointers when epilgoue_headp is changed
static void *lastNode;
//Size of the doubly linked free list.
static unsigned int listSize = 0;

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FITno

static char *heap_listp = 0;  /* Pointer to first block */  
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/**********************************
 ** BASIC CONSTANTS AND MACROS
**********************************/
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x3)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/**********************************
 ** HELPER FUNCTION DEFS
**********************************/
//Extend the heap by words words
static inline void *extend_heap(size_t words);
//Place block bp of size asize on the heap.
static inline void place(void *bp, size_t asize);
//Find a fit on the heap on which to allicate a block of size asize.
static inline void *find_fit(size_t asize);
//Coalesce the free blocks next to block bp.
static inline void *coalesce(void *bp);
//Print block bp.
static inline void printblock(void *bp); 
//Check block bp for consistency.
static inline void checkblock(void *bp);
//Check that the list of free blocks is consistent.
static inline void checkFreeList();

//Given a header h, calculate the header that h.previous points to
static inline void *prevPointerTarget(void *header);
//Given a header h, calculate the header that h.next points to
static inline void *nextPointerTarget(void *header);
//Given a masterHeader, set masterHeader.next to targetHeader
static inline void setNext(void *masterHeader, void *targetHeader);
//Given a masterHeader, set masterHeader.previous to targetHeader
static inline void setPrev(void *masterHeader, void *targetHeader);
//Get the offset of header from prologue_listp
static inline unsigned int getOffset(void *header);

//Given a header, add to the list of free nodes.
static inline void addNode(void *header);
//Delete the given node from the list of free nodes.
static inline void deleteNode(void *header);

/**********************************
 ** FUNCTIONS
**********************************/
/*
 * Initialize the heap: return -1 on error, 0 on success.
 */
int mm_init(void) {
	//Initialize globals
	prologue_headp = 0;
	epilogue_headp = 0;
	heap_listp = 0;
	lastNode = NULL;
	listSize = 0;
	
	/* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
		return -1;
	dbg_printf("here now\n");
	
	//Now, the alignment is prologue head, padding, prologue next.
	//This is to make prologue behave like a normal free cell. 
	PUT(heap_listp + (0*WSIZE), PACK(3*WSIZE, 1));             /* Prologue header */
    PUT(heap_listp + (1*WSIZE), 0);              /* Alignment padding */ 
    PUT(heap_listp + (2*WSIZE), 0);              /* Prologue next */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
	//Increment the appropriate pointers. 
	heap_listp += (2*WSIZE);    
	epilogue_headp += (3*WSIZE);          
	prologue_headp = (heap_listp - 2*WSIZE);
	dbg_printf("heap_listp address: %p\n", (void *)heap_listp);
	dbg_printf("two back from heap_listp: %p\n", (void *)heap_listp - 2*WSIZE);
	dbg_printf("size of prologue: %d\n", GET_SIZE(prologue_headp));
    
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
		return -1;

	//**mm_checkheap(1);
    return 0;
}

/*
 * malloc
 * Declare size number of bites on the heap.
 */
void *malloc (size_t size) {
	//**mm_checkheap(1);
	dbg_printf("Entering malloc\n");   
	size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *header;      

    if (heap_listp == 0){
		mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
		asize = 2*DSIZE;                                        
    else {
		//If asize would fit neatly into a block, make it happen.
		if ((size + WSIZE) % DSIZE == 0) {
			asize = (size + WSIZE);
		}
		//Otherwise, round it up to the nearest mult of DSIZE
		else {
			asize = DSIZE*((size + WSIZE + DSIZE) / DSIZE);
		}
	}
	dbg_printf("size: %Zu\n", size);
	dbg_printf("number of words: %d\n", ((int)asize) / 4);

    /* Search the free list for a fit */
    if ((header = find_fit(asize)) != NULL) {  
		place(header, asize);                  
		dbg_printf("Exiting malloc with match found.\n");
		return header + WSIZE;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                
    if ((header = extend_heap(extendsize/WSIZE)) == NULL) { 
		dbg_printf("Exiting malloc after extending heap with error\n");
		return NULL;                                 
	}
    place(header, asize);                                 
	dbg_printf("Exiting malloc after extending heap.\n");
    //**mm_checkheap(1);
    //Need to return the block pointer, which is WSIZE off the header.
	return header + WSIZE;
}

/*
 * free
 * Free the block at ptr from the heap.
 */
void free (void *ptr) {
	dbg_printf("Entering free.\n");
	dbg_printf("free: ptr to free = %p\n", HDRP(ptr));
	if(ptr == 0) 
		return;

    if (heap_listp == 0){
		mm_init();
    }

    addNode(HDRP(ptr));
	coalesce(HDRP(ptr));
	dbg_printf("Exiting free.\n");
}

/*
 * realloc - free the memory at oldptr and allocate size bytes
 */
void *realloc(void *oldptr, size_t size) {
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  newptr = malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  oldsize = *SIZE_PTR(oldptr);
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  free(oldptr);

  return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 * The same as malloc, but initializes the variables.
 */
void *calloc (size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap
 * Check the heap for consistency in a number of ways.
 * Very useful for debugging.
 */
void mm_checkheap(int verbose) {
	dbg_printf("###################\n");
	dbg_printf("###BEGIN CHECKHEAP\n");
	dbg_printf("###################\n");
	char *header = prologue_headp;

    if (verbose) {
		dbg_printf("Heap (%p):\n", header);
	}

	//Esnure the prologue is the proper size.
    if ((GET_SIZE(header) != 3*WSIZE)) {
		dbg_printf("Bad prologue header because its size is: %d\n", GET_SIZE(header));
	}
	//Ensure the prologue is allocated.
	if (!GET_ALLOC(header)) {
		dbg_printf("Bad prologue header because it's not allocated.\n");
	}

	//Check each block of memory on the heap.
    for (header = prologue_headp; GET_SIZE(header) > 0; header += GET_SIZE(header)) {
	if (verbose) {
	    printblock((void *)header);
	}
	checkblock((void *)header);
    }

    if (verbose) {
		printblock((void *)header);
	}
	//Ensure that the epilogue has a size of 0.
    if ((GET_SIZE(header) != 0)) {
		dbg_printf("Bad epilogue header because it's size is: %d\n", GET_SIZE(header));
	}
	//Ensure that the epilogue is allocated.
	if (!GET_ALLOC(header)) {
		dbg_printf("Bad epilogue block because it's not allocated.\n");
	}
	checkFreeList();
	dbg_printf("###################\n");
	dbg_printf("###LEAVING CHECKHEAP\n");
	dbg_printf("###################\n");
}

/*
 * Ensure that a block of memory is aligned at 8 bytes
 */
static inline void checkblock(void *header) 
{
    if ((((size_t)header)+4) % 8 != 0 && header != (void *)prologue_headp){
		dbg_printf("Error: %p is not doubleword aligned\n", header);
	}
}

/*
 * Print out the block of memory that starts at header.
 */
static inline void printblock(void *header) 
{
    size_t hsize, halloc;

    hsize = GET_SIZE(header);
    halloc = GET_ALLOC(header);  

    if (hsize == 0) {
		dbg_printf("Epilogue is next.\n");
    }

	//Print the block's address, it's size in words, and whether it's allocated.
    dbg_printf("%p: header: [size = %Zu: free = %c]\n", header, 
	hsize/4, (halloc ? 'a' : 'f')); 
}

/*
 * Check the doubly linked list of free blocks in memory for consistency.
 */
static inline void checkFreeList() {
	void *traverseHead = nextPointerTarget(prologue_headp);
	unsigned int index = 0;
	int verbose = 1;
	while (listSize != 0 && traverseHead != (void *)epilogue_headp) {
		dbg_printf("Member of free list: index = %d, pointer = %p, nextPointer = %p, prevPointer = %p\n"
			, index, traverseHead, nextPointerTarget(traverseHead), prevPointerTarget(traverseHead));
		if (traverseHead < mem_heap_lo() || (traverseHead > mem_heap_hi())) {
			dbg_printf("traverseHead if out of heap range!\n");
			exit(1);
		}
		if (traverseHead == (void *)prologue_headp) {
			dbg_printf("traverseHead is the prologue.\n");
			continue;
		}
		if (traverseHead == (void *)epilogue_headp) {
			dbg_printf("traverseHead is the epilogue.\n");
			continue;
		}
		//ERROR: No member of the free list should be allocated.
		if (GET_ALLOC(traverseHead)) {
			dbg_printf("Member of free list is allocated: index = %d\n", index);
		}
		//Print some additional information.
		if (verbose) {
			//Ensure that traverseHead.prev.next equals traverseHead (pointer consistency)
			if (nextPointerTarget(prevPointerTarget(traverseHead)) != traverseHead) {
				dbg_printf("traverseHead.prev.next != traverseHead, traverseHead = %p\n", traverseHead);
				exit(1);
			}
			//Ensure that traverseHead.next.prev equals traverseHead (pointer consistency)
			if (nextPointerTarget(traverseHead) != epilogue_headp) {
				if (prevPointerTarget(nextPointerTarget(traverseHead)) != traverseHead) {
					dbg_printf("traverseHead.next.prev != traverseHead, traverseHead = %p\n", traverseHead);
					exit(1);
				}
			}
		}
		index += 1;
		traverseHead = nextPointerTarget(traverseHead);
	}
	//Make sure that listSize accurately represents the number of elements in the list.
	if (index != listSize) {
		dbg_printf("listSize != index: listSize = %d, index = %d\n", listSize, index);
		exit(1);
	}
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
{
 */
static inline void *find_fit(size_t asize) {
	//Threshold used to determine first vs best fit.
	//size_t threshold = (1<<8)*WSIZE;
	int useFirstFit = 1;
	//If the block to allocate is large, use first fit.
	//if (asize > threshold) useFirstFit = 1;

	if (useFirstFit) {
		dbg_printf("Entering find fit.\n");
		void *traverseHead = nextPointerTarget(prologue_headp);
		dbg_printf("epilogue: %p, traverseHead: %p\n", (void *)epilogue_headp, traverseHead);
		while (traverseHead != (void *)epilogue_headp) {
			dbg_printf("Cur listSize: %d, cur headSize: %d\n", listSize, GET_SIZE(traverseHead));
			if (GET_SIZE(traverseHead) >= asize) {
				dbg_printf("Exiting find fit. Match found.\n");
				return (traverseHead);
			}
			traverseHead = nextPointerTarget(traverseHead);
		}
		dbg_printf("cur listSize: %d, cur headSize: %d\n", listSize, GET_SIZE(traverseHead));
		dbg_printf("Exiting find fit. No match found.\n");
		return NULL;
	}
	return NULL;

/*	//Perform best fit for small blocks.
	else {
		void *traverseHead = nextPointerTarget(prologue_headp);
		unsigned int headSize = GET_SIZE(traverseHead);
		unsigned int bestSize = ~0;
		void *bestPointer = NULL;
		unsigned int size = (unsigned int)asize;
		while (traverseHead != (void *)epilogue_headp) {
			if (headSize >= size && headSize - size <= bestSize) {
				bestPointer = traverseHead;
				bestSize = headSize - size;
				if (bestSize == 0) return bestPointer;
			}
			traverseHead = nextPointerTarget(traverseHead);
			headSize = GET_SIZE(traverseHead);
		}
		return bestPointer;
	}*/
}

/* 
 * place - Place block of asize bytes at start of new header 
 *         and split if remainder would be at least minimum block size
 */
static inline void place(void *header, size_t asize)
{
	dbg_printf("Entering place.\n");
	size_t csize = GET_SIZE(header);   
	//The neighbor to the right of header.
	void *nextNode = (header) + asize;
	dbg_printf("csize: %Zu, asize: %Zu\n", csize/4, asize/4);
	
	//Means we can split
    if ((csize - asize) >= (2*DSIZE)) {
		dbg_printf("place: in case where we have more free space than needed\n");
		deleteNode(header);
		PUT(header, PACK(asize, 1));
		PUT(nextNode, PACK(csize - asize, 0));
		addNode(nextNode);
    }
	//Means we have just enough memory to fit asize.
    else { 
		dbg_printf("place: in case where we have exactly enough free space\n");
		deleteNode(header);
		PUT(header, PACK(csize, 1));
    }
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static inline void *extend_heap(size_t words) 
{
	dbg_printf("Entering extend_heap with size %Zu\n", words);
	char *bp;
    size_t size;

	//Having a word size <= 2 will break my code
	if (words <= 2) return NULL;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	epilogue_headp = HDRP(NEXT_BLKP(bp)); /* update epilogue header */
	//Make sure the last node isn't pointing to the old epilogue_headp.
	if (listSize != 0) setNext(lastNode, epilogue_headp);
	dbg_printf("Calling add node\n");
	addNode(HDRP(bp));                    /* Add bp to list of free blocks */

	dbg_printf("Exiting extend_heap and entering coalesce.\n");
    /* Coalesce if the previous block was free */
    return coalesce(HDRP(bp));                                          
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * Because the free list is address- aligned, we should coalesce if two 
 * members of the list are adjacent.
 */
static inline void *coalesce(void *header) {
	dbg_printf("Entering coalesce\n");
	void *neighborToLeft = prevPointerTarget(header);
	void *neighborToRight = nextPointerTarget(header);
	size_t size = GET_SIZE(header);
	int leftFree = 0;
	int rightFree = 0;
	//Check conditions to determine if the left neighbor is a free block.
	if (!GET_ALLOC(neighborToLeft) && (neighborToLeft + GET_SIZE(neighborToLeft) == header)) {
		leftFree = 1;
	}
	//Check conditions to determine if the right neighbor is a free block.
	if (!GET_ALLOC(neighborToRight) && (header + size == neighborToRight)) {
		rightFree = 1;
	}

	//Case 1
	if (!leftFree && !rightFree) {
		dbg_printf("coalesce: Entering and exiting case 1\n");
		return header;
	}
	//Case 2
	else if (!leftFree && rightFree) {
		dbg_printf("coalesce: entering case 2\n");
		size += GET_SIZE(neighborToRight);
		setNext(header, nextPointerTarget(neighborToRight));
		PUT(header, PACK(size, 0));
		setPrev(nextPointerTarget(neighborToRight), header);
		dbg_printf("coalesce: exiting case 2\n");
		if (neighborToRight == lastNode) lastNode = header;
		listSize -= 1;
	}
	//Case 3
	else if (leftFree && !rightFree) {
		dbg_printf("coalesce: entering case 3\n");
		size += GET_SIZE(neighborToLeft);
		setNext(neighborToLeft, nextPointerTarget(header));
		PUT(neighborToLeft, PACK(size, 0));
		setPrev(nextPointerTarget(header), neighborToLeft);
		header = neighborToLeft;
		dbg_printf("coalesce: exiting case 3\n");
		if (header == lastNode) lastNode = neighborToLeft;
		listSize -= 1;
	}
	//Case 4 (both left and right are free)
	else {
		dbg_printf("coalesce: entering case 4\n");
		size += GET_SIZE(neighborToLeft) + GET_SIZE(neighborToRight);
		setNext(neighborToLeft, nextPointerTarget(neighborToRight));
		PUT(neighborToLeft, PACK(size, 0));
		setPrev(nextPointerTarget(neighborToRight), neighborToLeft);
		header = neighborToLeft;
		dbg_printf("coalesce: exiting case 4\n");
		if (neighborToRight == lastNode) lastNode = neighborToLeft;
		listSize -= 2;
	}
	
	dbg_printf("Exiting coalesce\n");
	return header;
}

//Given a header h, calculate the header that h.previous points to
static inline void *prevPointerTarget(void *header) {
	unsigned int prevPointerOffset = *((unsigned int *)(header + WSIZE));
	void *answer = (void *)(prologue_headp + prevPointerOffset);
	return answer;
}

//Given a header h, calculate the header that h.next points to
static inline void *nextPointerTarget(void *header) {
	unsigned int nextPointerOffset = *((unsigned int *)(header + 2*WSIZE));
	void *answer = (void *)(prologue_headp + nextPointerOffset);
	return answer;
}

//Given a masterHeader, set masterHeader.next to targetHeader
static inline void setNext(void *masterHeader, void *targetHeader) {
	unsigned int targetOffset = getOffset(targetHeader);
	*((unsigned int *)(masterHeader + 2*WSIZE)) = targetOffset;
}

//Given a masterHeader, set masterHeader.previous to targetHeader
static inline void setPrev(void *masterHeader, void *targetHeader) {
	unsigned int targetOffset = getOffset(targetHeader);
	*((unsigned int *)(masterHeader + WSIZE)) = targetOffset;
}

//Given a header, return its offset from prologue_headp
static inline unsigned int getOffset(void *header) {
	return (unsigned int)(header - (void *)prologue_headp);
}

//Add header to the list of free nodes.
static inline void addNode(void *header) {
	//Get the first element in the list.
	void *firstInList;
	unsigned int firstInListOffset;
	unsigned int headerOffset = getOffset(header);
	void *traverseHeader;
	void *traverseHeaderNext;
	void *twoBack = NULL;
	unsigned int traverseHeadNextOffset;

	dbg_printf("addNode: Node to add = %p\n", header);	
	//Special case 1: where this is the first member to add to the list.
	if (listSize == 0) {
		PUT(header, PACK(GET_SIZE(header), 0));
		setPrev(header, (void *)prologue_headp);
		setNext(header, (void *)epilogue_headp);
		setNext((void *)prologue_headp, header);
		lastNode = header;
		listSize += 1;
		dbg_printf("Added node to empty list.\n");
		return;
	}

	firstInList = nextPointerTarget((void *)prologue_headp);
	firstInListOffset = getOffset(firstInList);

	//Special case 2: header should be the new first element of the list
	if (headerOffset <= firstInListOffset) {
		dbg_printf("begin trying to add a node normally\n");
		PUT(header, PACK(GET_SIZE(header), 0));
		setNext(header, firstInList);
		setPrev(firstInList, header);
		setNext((void *)prologue_headp, header);
		setPrev(header, (void *)prologue_headp);
		listSize += 1;
		dbg_printf("Added node to front of non-empty list.\n");
		return;
	}
	//Special case 3: header should be the new last element of the list	
	if (headerOffset > getOffset(lastNode)) {
		PUT(header, PACK(GET_SIZE(header), 0));
		setNext(lastNode, header);
		//setPrev((void *)epilogue_headp, header);
		setNext(header, (void *)epilogue_headp);
		setPrev(header, lastNode);
		lastNode = header;
		listSize += 1;
		return;
	}
	
	if (listSize > 1) twoBack = prevPointerTarget(lastNode);
	//Special case 4: header should be the new second-to-last element of the list
	if (twoBack != NULL && headerOffset > getOffset(twoBack) && headerOffset < getOffset(lastNode)) {
		dbg_printf("addNode: In special case 4.\n");
		PUT(header, PACK(GET_SIZE(header), 0));
		setNext(twoBack, header);
		setPrev(header, twoBack);
		setNext(header, lastNode);
		setPrev(lastNode, header);
		listSize += 1;
		return;
	}
	traverseHeader = firstInList;
	traverseHeaderNext = nextPointerTarget(traverseHeader);
	traverseHeadNextOffset = getOffset(traverseHeaderNext);
	//Normal case: Traverse the list and find the first instance in which
	//curList.next > header
	while (traverseHeaderNext != (void *)epilogue_headp) {
		//Means we should place header between traverseHeader and traverseHeaderNext
		if (headerOffset <= traverseHeadNextOffset) {
			PUT(header, PACK(GET_SIZE(header),0));
			setNext(traverseHeader, header);
			setPrev(traverseHeaderNext, header);
			setNext(header, traverseHeaderNext);
			setPrev(header, traverseHeader);
			listSize += 1;
			dbg_printf("Added node to list in normal manner.\n");
			return;
		}
		//Otherwise, keep traversing the list
		traverseHeader = traverseHeaderNext;
		traverseHeaderNext = nextPointerTarget(traverseHeader);
		traverseHeadNextOffset = getOffset(traverseHeaderNext);
	}
}

/*
 * Delete the node at header from the list of free blocks.
 * This means the block at header has been allocated.
 */
static inline void deleteNode(void *header) {
	dbg_printf("Entering deleteNode.\n");
	void *prevNode;
	void *nextNode;
	PUT(header, PACK(GET_SIZE(header), 1));
	dbg_printf("deleteNode: node to delete = %p\n", header);
	//If there are no elements to delete, don't do anything.
	if (listSize == 0) {
		dbg_printf("Exit deleteNode because of listSize 0.\n");
		return;
	}
	//Special case where we're deleting the only element.
	else if (listSize == 1) {
		setNext((void *)prologue_headp, (void *)epilogue_headp);
		lastNode = NULL;
		listSize -= 1;
		dbg_printf("Location of header = %p\n", header);
		dbg_printf("Exit deleteNode because of listSize of 1.\n");
		return;
	}

	prevNode = prevPointerTarget(header);
	nextNode = nextPointerTarget(header);
	//Special case where we're deleting the last node in the list.
	if (nextNode == (void *)epilogue_headp) {
		setNext(prevNode, (void *)epilogue_headp);
		dbg_printf("deleteNode: prevNode = %p\n", prevNode);
		lastNode = prevNode;
		listSize -= 1;
		dbg_printf("Exit deleteNode after removing last node.\n");
		return;
	}
	//Special case where we're deleting the first node in the list.
	if (prevNode == (void *)prologue_headp) {
		setNext((void *)prologue_headp, nextNode);
		setPrev(nextNode, (void *)prologue_headp);
		listSize -= 1;
		dbg_printf("Exit deleteNode after deleting first node.\n");
		return;
	}
	//Normal case: we're deleting a node sandwiched in between 2 others.
	else {
		setNext(prevNode, nextNode);
		setPrev(nextNode, prevNode);
		listSize -= 1;
		dbg_printf("Exit deleteNode after removing node from the center of two nodes.\n");
		return;
	}
}
