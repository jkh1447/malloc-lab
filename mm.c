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

#define FirstFit 

/********************************************************
 * 명시적 가용 리스트-LIFO
 * 가용 블럭들을 링크드 리스트로 관리
 * 가용 블럭은 헤더+이전노드+다음노드+푸터로 구성됨
 * 할당된 블럭은 헤더+푸터로 구성됨
 * 
 * 
 * 
 * 
 ********************************************************/



/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12) //2^12 

#define MAX(x, y) ((x) > (y) ? (x) : (y))

// size비트와 alloc비트 or 연산, size의 마지막 3비트는 무조건 0이기 때문에 or 하면
// 하위 3비트에 alloc비트가 저장됨
#define PACK(size, alloc) ((size) | (alloc)) 

// p를 unsigned int타입 포인터로 캐스팅 후 간접 참조
// char* 이면 1 바이트만 수정가능하므로, 4바이트 데이터형으로 캐스팅하여 수정
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))

// 0x7: ... 0111, ~0x7: ... 1000, 하위 3비트 제외 모두 1이라서 사이즈비트만 추출
// p: 헤더나 푸터?
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// char 은 1바이트라서 1바이트 단위로 포인터 연산하기 위해
// bp: payload블록의 시작 포인터, 워드사이즈만큼 뒤로가면 헤더블록의 포인터
#define HDRP(bp) ((char *)(bp) - WSIZE)
// payload포인터에서부터 (블록 사이즈(헤더, 푸터 포함) - 더블워드사이즈(=헤더+푸터))
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록의 페이로드 포인터(?), GET_SIZE(HDRP(bp)) 로 대체 해도 되지 않나?
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 이전 블록의 페이로드 포인터, bp(payload 포인터)에서 더블워드만큼 뒤로 가면 
// 이전 블록의 푸터, 푸터안의 사이즈값을 추출해서 해당 값만큼 뒤로
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// bp는 void포인터 타입이므로 직접 간접참조 할 수 없다.
// 따라서 bp는 void * 타입을 가리키는 포인터라고 캐스팅하게 되면, bp 자체가
// 이중포인터라고 속이게(?) 되고, 간접참조 하게되면, 포인터는 항상 8바이트이기 때문에
// 그 주소를 가져올 수 있게 된다.
#define GET_PRED(bp) *(void **)(bp)
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void delete_from_freelist(void *bp);
static void add_freelist(void *bp);

static char* heap_listp;
static char* free_listp;

static void delete_from_freelist(void *bp){
    if(bp == free_listp){
        // 맨 앞에 있을경우
        free_listp = GET_SUCC(free_listp);
        return;
    }

    // 중간에 있을경우 
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    if(GET_SUCC(bp) != NULL) 
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);

}

static void add_freelist(void *bp){
    GET_SUCC(bp) = free_listp;
    // 가용리스트가 없을 수가 있다.
    if(free_listp != NULL)
        GET_PRED(free_listp) = bp;
    free_listp = bp;
}


static void *coalesce(void *bp){
    // 이전 블록의 푸터를 이용해 이전 블록의 할당여부를 구함
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 블록의 사이즈를 구함
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        add_freelist(bp);
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        // 합칠 다음 블럭의 크기
        delete_from_freelist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // free된 블록의 헤더의 size를 합친크기만큼 업데이트 해줌
        PUT(HDRP(bp), PACK(size, 0));
        // 바로 위에서 헤더의 size를 갱신했기 때문에, 푸터가 자동으로 
        // 다음 free 블럭의 푸터가 됨.
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){
        delete_from_freelist(PREV_BLKP(bp));
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        delete_from_freelist(NEXT_BLKP(bp));
        delete_from_freelist(PREV_BLKP(bp));
        // 원래 코드와 다름
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_freelist(bp);
    return bp;
}


static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // size가 홀수면 짝수로 보정, WSIZE 곱해서 8의배수로
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    // 반환타입이 포인터이기 때문에 long으로 캐스팅, long이면 캐스팅시 짤리는게 없기때문
    // bp에는 새로 할당된 힙공간의 시작 포인터
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    // bp는 새로 할당한 힙의 시작주소이고, 이 주소에서 1워드 앞으로 간 주소는 에필로그 블록이다.
    PUT(HDRP(bp), PACK(size, 0)); // 에필로그 블록에 헤더블록을 덮어씌움
    PUT(FTRP(bp), PACK(size, 0)); // 가용 블럭의 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //새로운 에필로그 블록

    return coalesce(bp);
    
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // mem_sbrk를 이용해 힙메모리를 할당하고, 실패하면 -1을 리턴하므로 init을 종료한다.
    if((free_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
        return -1;
    PUT(free_listp, 0); // 정렬을 위한 패딩
    PUT(free_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더, 크기가 8바이트, 할당된 블록
    PUT(free_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(free_listp + (3*WSIZE), PACK(4 * WSIZE, 0)); // 가용블럭 헤더
    PUT(free_listp + (4*WSIZE), NULL); // pred
    PUT(free_listp + (5*WSIZE), NULL); // succ
    PUT(free_listp + (6*WSIZE), PACK(4 * WSIZE, 0));
    PUT(free_listp + (7*WSIZE), PACK(0, 1)); // 에필로그 
    free_listp += (4 * WSIZE);

    /*
    if((free_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(free_listp, 0); // 정렬을 위한 패딩
    PUT(free_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더, 크기가 8바이트, 할당된 블록
    PUT(free_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(free_listp + (3*WSIZE), PACK(0, 1)); // 에필로그 
    free_listp = NULL;
    
    이렇게 해도 동작한다.
    */

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}


void place(void *bp, size_t size){
    delete_from_freelist(bp);
    size_t csize = GET_SIZE(HDRP(bp));
    if((csize - size) >= (2 * DSIZE)){
        // 배치 후 남은 블럭이 헤더+푸터+페이로드가 들어갈 최소크기보다 커야함.
        size_t new_free_size = csize - size;
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(new_free_size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(new_free_size, 0));
        add_freelist(NEXT_BLKP(bp));
    }
    else{
        // 위의 경우가 아니면 해당 가용블럭을 할당블럭으로만 변경한다.
        PUT(HDRP(bp), PACK(csize ,1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    
}

#ifdef FirstFit
static void *find_fit(size_t asize){
    char *bp = free_listp;
    while(bp != NULL){
        if(GET_SIZE(HDRP(bp)) >= asize)
            return bp;
        bp = GET_SUCC(bp);
    }
    return NULL;
}
#endif



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // size byte 할당
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0)
        return NULL;
    
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }
    else
        // 사이즈를 2워드 정렬하기 위해, 헤더와 푸터 4바이트, DSIZE: 헤더 + 푸터
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    } 

    // 1청크 사이즈 4096byte 보다 작으면 CHUNKSIZE가 항상 extendsize가 된다
    // 한 번 할당할때 4KB씩 크게 할당한다. 
    // asize는 헤더+페이로드+푸터를 고려한 값
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
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    //copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














