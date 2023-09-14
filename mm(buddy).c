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
#define SEGREGATED_SIZE (20) // segregated list의 class 개수

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // MAX를 찾아 리턴하는 함수

/* Pack a size and allocated bit into a word*/
#define PACK(size, alloc) ((size) | (alloc)) 
//PACK 매크로는 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴.

/*Read and write a word at address p*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))

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
#define ROOT(class) (*(void **)((heap_listp) + (WSIZE * class))) // root를 얻어옴

static void *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t a_size);
static void place(void *bp, size_t a_size);
static void removeBlock(void *bp); // 가용 리스트에서 제거
static void putFreeBlock(void *bp);    // 가용 리스트에 추가
static int get_class(size_t size); //class 를 얻어옴


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
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *) -1) // SEGREGATED_SIZE + 4 만큼 힙 영역 확장. +4의 의미는 [pad | p.h | p.f | e.h]
        return -1;

    PUT(heap_listp,0); //align padding - [0|p.h|p.f|e.h] 이렇게 더블 워드 조건을 만족시키기 위해. 이후 expand heap을 해도 차피 2워드씩 들어오니까.
    PUT(heap_listp + (1*WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE,1)); //프롤로그 헤더 (크기: 헤더 1 + 푸터 1 + segregated list 크기)
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE),NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));   // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치(끝 알림)

    heap_listp += DSIZE; // free_listp 가 가용 리스트 가리킴


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
    add_free_block(bp);                                      // 현재 블록을 free list에 추가
    size_t csize = GET_SIZE(HDRP(bp));                       // 반환할 사이즈
    void *root = heap_listp + (SEGREGATED_SIZE + 1) * WSIZE; // 실제 메모리 블록들이 시작하는 위치 (p.f 와 e.h 사이 payload)
    void *left_buddyp;                                       // 왼쪽 버디의 bp
    void *right_buddyp;                                      // 오른쪽 버디의 bp

    while (1)
    {
        // 좌우 버디의 bp 파악
        if ((bp - root) & csize) // 현재 블록에서 힙까지의 메모리 합(bp - root)과 csize가 중복되는 비트가 있다면 현재 블록은 오른쪽 버디에 해당
        {
            left_buddyp = bp - csize;
            right_buddyp = bp;
        }
        else
        {
            right_buddyp = bp + csize;
            left_buddyp = bp;
        }

        // 양쪽 버디가 모두 가용 상태이고, 각 사이즈가 동일하면 (각 버디가 분할되어있지 않으면)
        if (!GET_ALLOC(HDRP(left_buddyp)) && !GET_ALLOC(HDRP(right_buddyp)) && GET_SIZE(HDRP(left_buddyp)) == GET_SIZE(HDRP(right_buddyp)))
        {
            splice_free_block(left_buddyp); // 양쪽 버디를 모두 가용 리스트에서 제거
            splice_free_block(right_buddyp);
            csize <<= 1;                            // size를 2배로 변경
            PUT(HDRP(left_buddyp), PACK(csize, 0)); // 왼쪽 버디부터 size만큼 가용 블록으로 변경
            add_free_block(left_buddyp);            // 가용 블록으로 변경된 블록을 free list에 추가
            bp = left_buddyp;
        }
        else
            break;
    }
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * 경계태그 사용, 최소 블록 크기 16바이트, 묵시적 가용 리스트
 */
void *mm_malloc(size_t size)
{
    size_t asize = ALIGNMENT;//할당할 블록 사이즈
    size_t extendsize;
    void *bp;

    /*Ignore spurious requests*/
    if(size <= 0)
        return NULL;
    
    /* 사이즈 조정 */
    while(asize < size + DSIZE) // 요청받은 size에 8(헤더와 푸터 크기)를 더한 값을
    {
        asize <<= 1; //2의 n승이 되도록 올린다
    }
    //size + 8 을 한 값 보다 작을때까지 asize의 2의 지수승이 올라간다. 작을 때 한번 더 올리므로
    //asize는 결국 size를 2의 지수승으로 올린 결과이다.


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
    int class = get_class(asize); // size 에 맞는 class를 찾아 온 후
    void *bp = ROOT(class); //bp는 그 class의 root를 가리킴

    while (class < SEGREGATED_SIZE) 
    {
        bp = ROOT(class); //bp는 그 class의 root를 가리킴
        while (bp != NULL) // 그 class 안에서 bp가 null이 아닐동안
        {
            if((asize <= GET_SIZE(HDRP(bp)))) // class 안의 가용 블록을 찾음 - first fit
                return bp;
            bp = NEXT(bp); // 없으면 class 안에서의 다음 블록
        }
        class++; // 이 class를 전부 순회했는데도 없으면 다음 class로 넘어감
    }
    return NULL;    // NO fit
}

// 요청한 블록을 배치, 필요한 경우 블록 분할
static void place(void *bp, size_t a_size) { // 할당할 위치의 bp, 사용할 양
    size_t c_size = GET_SIZE(HDRP(bp)); //사용하려는 블록의 크기
    //c_size = find_fit 으로 받아온 메모리 size, a_size = 내가 할당하려고 하는 메모리 size

    //할당블록은 freelist에서 지운다
    removeBlock(bp);

    while(a_size != c_size) // 사용하려는 a_size와 블록의 크기 c_size가 다르면 분할
    {
        c_size >>= 1; // 블록의 크기 반으로 나눔
        PUT(HDRP(bp + c_size), PACK(c_size,0)); // 뒷부분을 가용 블록으로 변경
        putFreeBlock(bp + c_size); // 뒷부분을 가용 블록 리스트에 추가
    }
    PUT(HDRP(bp), PACK(c_size,1)); // 크기가 같아지면 해당 블록 사용 처리
}

// 적합한 가용 리스트의 클래스를 찾아서 맨 앞에 현재 블록(할당 해제되거나 새로 추가된 가용 블록)을 추가하는 함수
static void putFreeBlock(void *bp){
    int class = get_class(GET_SIZE(HDRP(bp)));
    NEXT(bp) = ROOT(class); // 루트를 현재 블록의 뒤로 보냄 (NULL이어도 상관x)
    if(ROOT(class) != NULL) // list에 블록이 존재했을 경우만
        PREV(ROOT(class)) = bp; // 루트였던 블록의 PREV를 추가된 블록으로 연결
    ROOT(class) = bp; // 방금 추가한 블록이 루트가 됨
}

// 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void removeBlock(void *bp){
    int class = get_class(GET_SIZE(HDRP(bp)));
    if(bp == ROOT(class)) // 분리하려는 블록이 이 class의 리스트의 맨 앞에 있는 블록이면(즉 이전 블록이 없으면)
    {
        ROOT(class) = NEXT(ROOT(class)); // 다음 블록을 이 클래스의 루트로 변경
        return;
    }

    NEXT(PREV(bp)) = NEXT(bp);  // 이전 블록의 NEXT를 다음 가용 블록으로 연결 (NULL이어도 상관 x)

    if(NEXT(bp) != NULL) //다음 가용 블록이 존재할 때
        PREV(NEXT(bp)) = PREV(bp); //다음 블록의 PREV는 이전 블록이다.
}

// 적합한 가용 리스트를 찾는 함수 -> builtin_clt 쓰는 방식 &&&
int get_class(size_t size)
{
    size_t n;
    n = 31 - __builtin_clz((unsigned int)(size));
    //제일 왼쪽 1이 있는 지수 승을 찾아줌. 이 지수승은 class를 찾는데 쓰임.
    //예를 들어 size가 8(2진수로 1000)이면 n은 3가 된다.
    //만약 size가 15(2진수로 1111)라고 해도 2의 4승이 안되기 때문에 n이 3가 된다.
    //그렇기 때문에 맨 왼쪽 1만 찾으면 된다.

    if(size == (1<<n)) // 1<<n 은 1을 왼쪽으로 n번 옮기는 것이므로 2의 n승이 된다.
        return n; //만약 size가 2의 n승과 동일하다면 n이 class 가 된다.
    else   // 동일하지 않다면 class는 n + 1 이 된다. 예를들어 class 4는 2^3 부터 2^4 까지만 되기 때문이다.
        return n + 1; 
}

// // 적합한 가용 리스트를 찾는 함수 -> builtin_clt 안 쓰는 방식
// int get_class(size_t size)
// {
//     /*
//     첫번째 가용 리스트의 최소 크기는 블록의 최소 크기인 16bytes로 설정하고,
//     다음 단계로 넘어갈수록 최소 크기가 이전 가용 리스트의 2배가 될 때
//     현재 size에 적합한 가용 리스트를 찾는다.
//     */

//     // 클래스 별 최소 크기
//     size_t class_sizes[SEGREGATED_SIZE];
//     class_sizes[0] = 0;

//     int a = 31 - __builtin_clz((unsigned int)size);

//     //주어진 크기에 적합한 클래스 검색
//     for(int i = 0; i < SEGREGATED_SIZE; i++)
//     {
//         class_sizes[i] = class_sizes[i - 1] << 1;
//         if (size <= class_sizes[i]) // <2>
//             return i;
//     }

//     /*
//     <2> i = 0 일 때, size가 class_sizes[0](16)보다 같은지 (16보다 작을 수는 없으니까) 확인하고,
//     <1> 16보다 크면 i = 1이 되므로 <1>로 들어가서 class_sizes[1] 은 16의 2배 즉 32가 된다. 이후
//     <2> 다시 32보다 같거나 작은지(16보다는 큼) 확인한다.
//     위 방법을 i가 SEGREGATED_SIZE보다 작을 동안 반복되며(즉 class 수 만큼), 알맞는 size를 찾으면 그 class를 리턴한다.
//     */

//     return SEGREGATED_SIZE - 1; // 위 반복동안 알맞는 class 를 못 찾았으면, 마지막 class를 리턴한다. 마지막 클래스는 ~inf 까지기 때문이다.
// }


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); //지금 블록의 size를 갖고온 다음

    PUT(HDRP(bp), PACK(size, 0)); //지금 블록의 헤더 할당 없앰
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