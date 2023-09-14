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
    "week05",
    /* First member's full name */
    "SeungtaeJeon",
    /* First member's email address */
    "poqop721@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT @@@*/
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t 의 사이즈(byte) @@@

#define WSIZE 4 // Word size - header/footer size (bytes)
#define DSIZE 8 // Double word size (bytes)
#define CHUNKSIZE (1<<12) // Extend heap by this amount (bytes)
//2^12 = 4096 => 4096 바이트 만큼 힙을 증가시킴

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // MAX를 찾아 리턴하는 함수

/* Pack a size and allocated bit into a word*/
#define PACK(size, alloc) ((size) | (alloc)) 
//PACK 매크로는 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴.

/*Read and write a word at address p*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/*Read the size and allocated fields from address p*/
#define GET_SIZE(p) (GET(p) & ~0x7) //주소 p에 있는 헤더 또는 풋터의 size 리턴
// ~0x7 은 000 이므로 뒤 3비트를 0으로 초기화 시켜서 size만 갖고옴
#define GET_ALLOC(p) (GET(p) & 0x1) //주소 p에 있는 헤더 또는 풋터의 할당 비트 리턴
// 0x1은 1 이므로 맨 뒤 alloc 정보만 갖고올 수 있음 

/*Given block ptr bp, compute address of its header and footer*/
//bp는 payload의 시작 주소 가리킴
#define HDRP(bp) ((char *)(bp) - WSIZE) //header address
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)// footer address
//payload 를 가리키는 bp에서 1블록만큼 가면 다음 블록의 payload를 가리킬텐데, 거기서 2워드(헤더,푸터) 만큼 뺌

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char * )(bp) - WSIZE))) //다음 bp를 가리킴
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char * )(bp) - DSIZE))) // 이전 bp를 가리킴

/*void**는 void형 포인터의 주소를 저장한다.
void*는 자료형에 관계없이 주소값을 대입할 수 있는 포인터, 
void**는 그 void형 포인터의 주소를 가리킴.
void** 는 void*를 가리키며 void*는 포인터형 변수이므로 4byte의 크기를 가진다.
*(void**) => void형 포인터의 주소의 값 => 4byte
*/
#define PREV(bp) (*(void**)(bp)) // bp는 prev를 가리킴.
#define NEXT(bp) (*(void**)(bp + WSIZE))// 위 + WSIZE

static void *heap_listp;
static char *free_listp; // free list head - 가용리스트 시작부분  
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);
void removeBlock(void *bp);
void putFreeBlock(void *bp);


/*
 * mm_init - initialize the malloc package. 할당기 초기화
 시스템에서 4워드를 가져와서 빈 가용 리스트를 만들 수 있도록 초기화
 */
int mm_init(void)
{
    /*create the initial empty heap*/
    /* padding 4byte(1byte는 alloc) + 프롤로그 헤더 4byte / prev(4byte) + next(4byte)
    /프롤로그 풋터 4byte + 에필로그 헤더 4byte / => 24byte
    */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *) -1) // 24byte
        return -1;

    //[ padding | p.h | prev | next | p.f | e.h ]
    PUT(heap_listp,0); //align padding - [0|p.h|p.f|e.h] 이렇게 더블 워드 조건을 만족시키기 위해. 이후 expand heap을 해도 차피 2워드씩 들어오니까.
    PUT(heap_listp + (1*WSIZE), PACK(ALIGNMENT,1)); //프롤로그 헤더 16/1
    PUT(heap_listp + (2*WSIZE), 0); //프롤로그 PREV 포인터 NULL로 초기화
    PUT(heap_listp + (3*WSIZE), 0); //프롤로그 NEXT 포인터 NULL로 초기화
    PUT(heap_listp + (4*WSIZE), PACK(ALIGNMENT, 1)); //프롤로그 풋터 16/1
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); //에필로그 헤더 0/1

    free_listp = heap_listp + DSIZE; // free_listp 가 prev 포인터를 가리키게 초기화

    /*Extend the empty heap with a free block of CHUNKSIZE bytes*/
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) // CHUNKSIZE 바이트를 워드 사이즈로 변환(인자가 word라서)
        return -1;
    return 0;
}

/*extend_heap 은 다음 두 경우에 호출됨
1. 힙이 초기화될 때
2. mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때.
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /*Allocate an even number of words to maintain alignment 
    정렬을 유지하기 위해 요청한 크기를 인접 2워드의 배수(8바이트)로 반올림*/ 
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 
    // 짝수면 +1 해서 홀수로(내부단편화), 홀수면 그냥 바로.
    if ((long)(bp = mem_sbrk(size)) == -1) //sbrk로 힙 확장 -> bp
        return NULL;

    /*Initiallize free block header/footer and the epilogue header*/
    PUT(HDRP(bp), PACK(size,0)); /*free block header*/
    PUT(FTRP(bp), PACK(size,0)); /*free block footer*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*new epilogue header*/

    /*위에서 mem_sbrk를 통해 새로운 블록을 생선한다고 해도 리턴되는 값은 old_brk이다.
    이 old_brk는 이전 에필로그 헤더를 가리키고 있다.
    이때 PUT(HDRP(bp), PACK(size,0)); 를 통해 이 헤더는 0으로 초기화되면서 새로운 블록의 헤더가 되고, 이 헤더부터 chunksize 만큼의 뒤는 footer가 된다.
    그리고 그 다음 블록은 새로운 에필로그 헤더가 된다.
    이렇게 기존 에필로그 헤더를 할당 해제 시키고 새로운 에필로그 헤더를 만든다.
    */

    /*Coalesce if the previous block was free*/
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));//이전 블록의 풋터를 통해 이전 블록이 할당되었는지.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록의 헤더를 통해 다음 블록이 할당되었는지.
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈

    /*(case 1 - 전후 다 할당) 삭제. -> 가용 블록이 없으면 조건을 추가할 필요가 없음. 맨 밑에서 root에 삽입함*/

    /*case 2 - 전은 할당, 후는 비할당*/
    if(prev_alloc && !next_alloc){
        removeBlock(NEXT_BLKP(bp)); //
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); //현재 size + 다음 size
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }

    /*case 3 전 비할당, 후 할당*/
    else if(!prev_alloc && next_alloc){
        removeBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); //현재 size + 이전 size
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp); // bp는 이전 블록의 payload를 가리키게
        // bp = PREV_BLKP(bp);
        // PUT(HDRP(bp), PACK(size,0));
        // PUT(FTRP(bp), PACK(size,0));
    }

    /*case 4 전후 다 비할당*/
    else if(!prev_alloc && !next_alloc){
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        //현재 size + 이전 size + 다음 size
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp); // bp는 이전 블록의 payload를 가리키게
    }
    putFreeBlock(bp); // 연결이 된 블록을 free list 에 추가
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * 경계태그 사용, 최소 블록 크기 16바이트, 묵시적 가용 리스트
 */
void *mm_malloc(size_t size)
{
    size_t asize;//할당할 블록 사이즈
    size_t extendsize;
    void *bp;

    /*Ignore spurious requests*/
    if(size <= 0)
        return NULL;
    
    /*adjust block size to include overhead and alignment reqs.*/
    if(size <= DSIZE)
        asize = 2*DSIZE; // 2워드 이하의 사이즈는 4워드로 할당 요청 (header 1word, footer 1word, 2word는 정렬 조건을 만족시키기 위해)
    else  // 할당 요청의 용량이 2words 초과 시, 충분한 8byte의 배수의 용량 할당
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
        /*1. size에 DSIZE(헤더 + 풋터)를 더한다.
          2. 1.에 DSIZE - 1을 더하고, 이 결과를 DSIZE로 나누어서 나머지를 제거. 여기에 DSIZE 곱함 => DSIZE의 배수로 반올림됨.
             ex) size = 20, DSIZE = 8
                1. size + DSIZE = 28
                2. (28 + 7)/8 을 하면 나머지 3은 날라가기 몫 4만 남음. 이 몫에 DSIZE 를 곱하면 32가 됨.
                    즉 28을 8의 배수로 반올림 한 32가 됨.
        */

    /*Search the free list for a fit*/
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    /*No fit found. Get more memory and place the block*/
    extendsize = MAX(asize, CHUNKSIZE); //이렇게 하면 메모리 할당자가 효율적으로 메모리를 확장하고 오버헤드를 최소화 -> 외부 단편화를 방지
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


// First Fit
static void *find_fit(size_t asize) {
    void *bp;

    //가용리스트의 시작부터;할당이 안 됐을 동안;bp는 다음 블록으로 넘어가면서)
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = NEXT(bp)) {
        //내가 요청한 size보다 클 때 => 적합
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;    // NO fit
}

// 요청한 블록을 배치, 필요한 경우 블록 분할
static void place(void *bp, size_t a_size) {
    size_t c_size = GET_SIZE(HDRP(bp)); //(기존에 할당되었던 곳의) 할당할 블록의 전체 사이즈
    //c_size = find_fit 으로 받아온 메모리 size, a_size = 내가 할당하려고 하는 메모리 size

    //할당블록은 freelist에서 지운다
    removeBlock(bp);

    // csize에 asize를 쓰고도 4워드 이상 남는다면, 그 4워드를 나중에 또 쓸 수 있게 처리
    if ((c_size - a_size) >= (2 * (DSIZE))) {
        // 요청 용량 만큼 블록 배치 & alloc 처리
        PUT(HDRP(bp), PACK(a_size, 1));
        PUT(FTRP(bp), PACK(a_size, 1));
        
        bp = NEXT_BLKP(bp);
        // 남은 블록에 header, footer 배치, 가용상태 처리
        PUT(HDRP(bp), PACK(c_size - a_size, 0));
        PUT(FTRP(bp), PACK(c_size - a_size, 0));
        putFreeBlock(bp);// free list 첫번째에 분할된 블럭을 넣는다.
    }
    else {      // csize와 aszie 차이가 네 칸(4워드,16byte)보다 작다면 해당 블록 통째로 사용
        PUT(HDRP(bp), PACK(c_size, 1));
        PUT(FTRP(bp), PACK(c_size, 1));
    }
}

// LIFO 방식으로 새로 반환되거나 생성된 가용 블록을 가용리스트 맨 앞에 추가
void putFreeBlock(void *bp){
    NEXT(bp) = free_listp; // 가용 블록 다음이 가용리스트 -> 맨 앞으로 보냄
    PREV(bp) = NULL; // 맨 앞이니까 가용 블록의 prev는 null
    PREV(free_listp) = bp; // 가용 리스트의 prev는 이제 가용 블록
    free_listp = bp; // 가용리스트의 시작 주소를 가용 블록의 시작 주소로 바꿔줌
}

//free list 맨 앞에 프롤로그 블록이 존재
void removeBlock(void *bp){
    //첫 번째 블록을 없앨 때
    if(bp == free_listp){
        PREV(NEXT(bp)) = NULL; // (bp의 next 블록) 의 이전 블록은 이제 null이다. 즉 (bp의 next 블록)이 이제 시작 블록이다.
        free_listp = NEXT(bp); // free_list의 시작 주소를 다음 블록의 시작 주소로 바꿔줌
    } else { //첫 번째 블록이 아닐 때 블록 삭제
        NEXT(PREV(bp)) = NEXT(bp);
        PREV(NEXT(bp)) = PREV(bp);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); //지금 블록의 size를 갖고온 다음

    PUT(HDRP(bp), PACK(size, 0)); //지금 블록의 헤더 할당 없앰
    PUT(FTRP(bp), PACK(size, 0)); //지금 블록의 풋터 할당 없앱
    coalesce(bp); //연결함
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 새로운 블록을 할당하고, 기존 데이터를 복사하여 이 새로운 블록으로 옮긴다. 
 */
void *mm_realloc(void *bp, size_t size)
{
    void *old_bp = bp;
    void *new_bp;
    size_t copySize;

    if (size <= (GET_SIZE(HDRP(bp))-DSIZE)){ // 요청한 size가 더 작으면 그냥 원래 그대로 리턴(확장x)
        return bp;
    }
    if (GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0 && (GET_SIZE(HDRP(bp))-DSIZE) + GET_SIZE(HDRP(NEXT_BLKP(bp))) > size){ // 맨 앞 가용블록이 size보다 작으면 그 뒤 가용 블록과 연결 처리
        //다음 블록이 가용 블록이고 && (현재 가용 블록 사이즈 + 다음 블록의 사이즈)가 size 보다 크면 (즉 병합 가능할 때)
        removeBlock(NEXT_BLKP(bp)); //다음 가용 메모리의 연결을 끊고(없다 처리하고)
        size_t sum = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록과 다음 가용 블록을 연결
        PUT(HDRP(bp), PACK(sum,1));
        PUT(FTRP(bp), PACK(sum,1));
        return bp;
    }
    
    new_bp = mm_malloc(size); // 말록으로부터 새로운 메모리를 할당 받아 온 후 (bp 리턴)
    if (new_bp == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(old_bp)); // 기존 블록의 size를 copysize에 저장
    memcpy(new_bp, old_bp, copySize);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 copySize만큼의 문자를 new_bp로 복사해라)
    mm_free(old_bp); // 이전 블록은 해제
    return new_bp; 
}