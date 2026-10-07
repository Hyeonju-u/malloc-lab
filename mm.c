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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};
// mm_init으로 힙 틀을 만든 뒤, malloc은 find_fit찾기 → expend_heap 없으면 늘리기 → place 자르기, free는 표시 지우기 → 합치기를 반복하는 구조
//  정렬 단위 malloc 이 돌려주는 주소와 블록 크기는 모드 8의 배수여야한다
#define ALIGNMENT 8 // ALIGNMENT 정렬조건을 8바이트로 설정함
// size를 8의 배수중 가장 가까운 큰 값으로 올린다

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 주어진 사이즈를 ALIGNMENT의 배수로 올린다 즉 8바이트로 정렬 size가 8이면 8+8-1= 15 & ~0x7 먼저 사이즈에 7을 더해서 다음 8의 배수를 넘기게 만든 뒤 ~0x7 과 and해서 아래 3비트를 0으로 지운다.

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
// SIZE_T_SIZE size_t 타입의 크기를 8바이트 배수 로 정렬해서 알려준다

#define WSIZE 4             // 헤더 풋터 1칸 크기
#define DSIZE 8             // 정렬 단위 (WSIZE*2)
#define CHUNKSIZE (1 << 12) // 힙이 모자를때 늘릴크기(4096바이트)
#define MINBLOCK 24

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 두 값중 가장 큰값

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define SUCC(bp) (*(void **)((char *)(bp) + DSIZE)) // 다음 프리 블록 주소 내 앞에있는 빈 블록의 주소
#define PRED(bp) (*(void **)(bp))                   // 이전 프리 블록 주소 내 뒤에있는 빈 블록의 주소

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 내 bp에서 8칸 앞(앞 블록의 푸터)에 적힌 크기를 읽고 그만큼 뒤로 가라
#define FIRST_FIT 0
#define NEXT_FIT 1
#define BEST_FIT 2

#ifndef FIT_POLICY
#define FIT_POLICY FIRST_FIT
#endif

static char *heap_listp;        // 힙의 시작점(프롤로그 블록)을 가리킬 포인터
static void *free_listp = NULL; // free list의 시작 주소 --추가
#if FIT_POLICY == NEXT_FIT
static char *rover; // 다음 탐색을 시작할 위치 (마지막으로 찾은 블록의 Bp)
#endif
static void *extend_heap(size_t words);    // 힙늘리기
static void *find_fit(size_t asize);       // 들어갈 빈 블록 찾기
static void place(void *bp, size_t asize); // 찾은 블록에 할당 표시
static void *coalesce(void *bp);           // 앞 뒤 빈 블록 합치기
static void insert_free(void *bp);         // 빈 블록 bp를 맨앞에 넣는다
static void remove_free(void *bp);         // 빈 블록 bp를 리스트에서 뺀다 (앞뒤를 이어붙임)

// 힙 탐색의 출발점 mm_init 힙의 기본틀(패딩,에필로그,프롤로그)을 세우고 처음 쓰 빈 빈블록 4096 바이트를 확보한다 성공 0 실패 -1

int mm_init(void) // 힙을 처음 세팅
{

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1; // 힙을 16바이트 워드 4칸을 늘림 mem_sbrk는 늘리기전 힙의 끝 주소를 돌려줌

    PUT(heap_listp, 0);                            //[칸0] 정렬용 패딩 의미없는 0 이바이트가 있어야 이후 블록블이 bp가 8의 배수 자리에 옴
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); //[칸1]프롤로그헤더 크기 8 할당됨 9
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); //[칸2]프롤로그 푸터 크기 8, 할당됨 9
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     //[칸3] 에필로그 헤더 크기 0,할당됨 1 사용중

    // heap_listp를 프롤로그 블록 위치로 옮기기
    // malloc 코드에는 블록을 가르킬때는 항상 헤더 바로 뒤(playload 시작점)을 가르킨다 라는 약속이있음
    heap_listp += (2 * WSIZE); // 8바이트 앞으로->프롤로그 헤더와 푸터 사이를 가리킴
    free_listp = NULL;
#if FIT_POLICY == NEXT_FIT
    rover = heap_listp; // 처음에 힙 맨 앞 프롤로그에서 시작
#endif
    //  실제로 쓸 빈 블록 붙이기
    //  CHUNKSIZE /WSIZE = 4096 /4 = 1024->1024 워드만큼 늘려줌
    //  extend_heap은 바이트가 아니라 워드 개수를 받기때문에 바이트->워드 단위로 바꿔주기
    //  extend_heap 안에서는 워드->바이트로 되돌림 1024*4 = 4096
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}
// heap 끝에 words개 워드만큼 새 빈블록을 붙인다  성공시 새빈블록의 bp 실패시 NULL 호출되는때:mm_init mm_ malloc이 맞는 블록을 못 찾았을때
static void *extend_heap(size_t words) // 힙 확장해주는 곳
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // 워드 개수를 짝수로 맞춘뒤 바이트로 바꿈 짝수워드 8의배수 바이트->블록크기 정렬유지
    // words = 5    → 5 % 2 = 1(홀수)    → (5 + 1) * 4 = 24
    if ((long)(bp = mem_sbrk(size)) == -1)
        // Heap 을 사이즈 바이트 늘린다 bp= 늘리기전 힙의 끝주소 주소를 long으로 바꿔서 -1과 비교
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새 빈 블록의 헤더 이자리는 원래 에필로그가 있던칸 에필로그를덮어써서 헤더로 재사용
    PUT(FTRP(bp), PACK(size, 0));         // 새 빈 블록의 풋
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 페에필로그 다음블록의 헤더자리

    return coalesce(bp); // 힙 끝에 있던 마지막 블록이 비어있었다면 새블록과 합친다 mm_init 직후엔 앞이 프롤로그(할당됨)라서 합칠게없음 그대로 bp반환
}
#if FIT_POLICY == FIRST_FIT
static void *find_fit(size_t asize)
// asize 이상인 빈블록을 힙 앞에서부터 찾는다 반환 찾은 블록의 bp,없으면 NULL
{

    void *bp;
    for (bp = free_listp; bp != NULL; bp = SUCC(bp)) // 시작 힙리스트,조건 헤더 크기가 0보다 큰동안 크기0인에필로그를 만나면 끝 이동:다음 블록으로  1회차: 프롤로그 → 할당됨 → 통과 2회차: A→ 할당됨 → 통과 3회차: B → 빈 블록 && 4072 >= 16 → B의 bp 반환
    {
        if (GET_SIZE(HDRP(bp)) >= asize)
        { // 비어있고 alloc 크기가 충분하면 이블록사용
            return bp;
        }
    }
    return 0; // 수정전 0
}
#elif FIT_POLICY == NEXT_FIT
static void *find_fit(size_t asize)
{
    char *oldrover = rover; // 이번 탐색을 시작한 위치 기억
    for (; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && GET_SIZE(HDRP(rover)) >= asize)
        { // 비어있고 alloc 크기가 충분하면 이블록사용
            return rover;
        }
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && GET_SIZE(HDRP(rover)) >= asize)
        {
            return rover;
        }
    return NULL;
}
#elif FIT_POLICY == BEST_FIT
static void *find_fit(size_t asize)
{
    void *bp;
    void *best = NULL;
    size_t best_size = (size_t)-1;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        size_t bsize = GET_SIZE(HDRP(bp));

        if (!GET_ALLOC(HDRP(bp)) && bsize >= asize)
        {
            if (bsize == asize)
                return bp;
            if (bsize < best_size)
            {
                best = bp;
                best_size = bsize;
            }
        }
    }
    return best;
}
#endif
static void insert_free(void *bp) // free된 빈 블록 bp를 맨앞에 넣는다
{
    SUCC(bp) = free_listp;
    PRED(bp) = NULL;           // bp가 맨앞이니까 이전(뒤)는 없음
    if (free_listp != NULL)    // free 시작 리스트가 null이면
        PRED(free_listp) = bp; // 이전 블록에 bp주소를
    free_listp = bp;           // 그게 아니면 free시작 리스트에 bp주소를
}
// 더이상 빈 블록이 아니게될때 호출 블록이 리스트에 있을 자격을 잃을때 빼주는함수
// 1)place에 할당될때 2) 다른 빈 블록과 합쳐질때
static void remove_free(void *bp) // 빈 블록 bp를 리스트에서 뺀다
{
    if (PRED(bp) != NULL)
        SUCC(PRED(bp)) = SUCC(bp); // 앞블록의 다음 = 내다음
    else
        free_listp = SUCC(bp);
    if (SUCC(bp) != NULL)
        PRED(SUCC(bp)) = PRED(bp);
}

// find_fit이 찾아준 빈 블록에 할당됨 도장을 찍는데 블록이 요청보다 많이 크면 필요한 만큼 잘라쓰고 나머지는 빈 블록으로 남기는 함수
static void place(void *bp, size_t asize)
{
    remove_free(bp);
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 빈 블록의 전체 크기
    // // 남는 부분이 최소 블록크기 16=(헤더4+풋터 4+플레이로드 8) 이상이면 쪼갠다
    // // 16보다 작으면 독립된 블록을 만들수 없으니 쪼개지않는다
    if (csize - asize >= 2 * MINBLOCK)
    { // case 1:쪼개는 경우 /* Case 1: 쪼개는 경우 예) csize = 4096, asize = 24 → 남는 크기 4072 >= 16 → 쪼갬 [앞부분 24/1][뒷부분 4072/0]
      // 앞부분 요청 크기만큼 할당
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp); // bp를 뒷부분의 시작으로이동(방슴 쓴 헤더의 크기 24만큼 이동)
        // 뒷부분 남은 크기만큼 빈블록

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        insert_free(bp);
    }
    else // 쪼개지않는 경우->블록 전체를 할당 예) csize = 32, asize = 24 → 남는 크기 8 < 16 → 통째로 사용 (8바이트는 내부 단편화로 낭비된다)
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
void *mm_malloc(size_t size)
{
    size_t asize;      // 요청 사이즈 헤더+풋터 정렬을 반영한 실제 블록 크기
    size_t extendsize; // 맞는 블록 없을때 힙을 늘릴 크기
    char *bp;
    if (size == 0) // 0바이트 요청은 무시
        return NULL;
    if (size <= MINBLOCK) // 실제 블록 크기 계산  size <= 8 → 최소 블록 16 (헤더4 + payload8 + 풋터4)
        asize = 2 * MINBLOCK;
    else
        asize = MINBLOCK * ((size + (MINBLOCK) + (MINBLOCK - 1)) / MINBLOCK);
    if ((bp = find_fit(asize)) != NULL) // 맞는 빈 블록이 있으면 거기에 할당하고 끝
    {
        place(bp, asize);
        return bp;
    }
    // 없으면 힙을 늘린다 요청이 4096보다 크면 요청 크기만틈 아니면 4096만틈 늘림
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize); // 새로얻은 블록에 할당 표시
    return bp;
}
void mm_free(void *bp) // 블록을 빈 블록으로 표시하고 앞뒤 빈 블록과 합침
{                      // 이 블록의 크기를 헤더에서 읽는다
    size_t size = GET_SIZE(HDRP(bp));
    // 헤더와 풋터의 할당 비트를 0으로 바꾼다(크기는 그대로) 예) 24/1 (값 25) → 24/0 (값 24)

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp); // 앞뒤가 비어있으면 합친다 외부 단편화 줄이기
}
static void *coalesce(void *bp) // free 직후에 불림 Bp블록 앞뒤 블록이 비어있으면 하나로 합친다 반환:합쳐진 블록의 Bp(앞블록과 합치면 bp가 앞으로 이동함) 합친블록이 앞 블록부터 시작해야함 내 양옆 이웃을 검사하는변수 내 bp 검사 x
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 이전 블록의 풋터에서 할당 여부 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 다음 블록의 헤더에서 할당 여부 확인
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 크기

    if (prev_alloc && next_alloc) // 두개 다 참(할당됨)이면
    {                             ///* Case 1: [할당][나][할당] → 합칠 게 없음 */
    }
    else if (prev_alloc && !next_alloc) // Case 2: [할당][나][빈] → 뒤 블록과 합침 예) 나 16 + 뒤 32 = 48 다른 빈 블록들과 합쳐질때 나와 합쳐져서 독립된 블록으로 없어질 예정 없어지기 전에 미리 명단에서 지움
    {
        remove_free(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // size += 현재 블록 크기+ 뒤 블록 크기
        PUT(HDRP(bp), PACK(size, 0));          // 프리 직후에 불리고 next_alloc이 할당 안된거니까 빈블록 생겼다고 기록
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        remove_free(PREV_BLKP(bp));
        // Case 3: [빈][나][할당] → 앞 블록과 합침 합친 블록은 앞 블록 위치에서 시작 → bp를 앞으로 옮김 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // size += 현재 블록 크기+ 이전 블록 크기
        PUT(FTRP(bp), PACK(size, 0));            // 내푸터 위치(현재bp)에 사이즈,비어있음
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 내헤더 위치(이전bp위치)에 사이즈,비어있음
        bp = PREV_BLKP(bp);                      // 합친 블록의 시작이 이제 앞블록임
    }

    else // Case 4: [빈][나][빈] → 앞, 나, 뒤 셋을 합침 예) 앞 32 + 나 16 + 뒤 24 = 72 시작 = 앞 블록 헤더, 끝 = 뒤 블록 풋터
    {
        remove_free(NEXT_BLKP(bp));
        remove_free(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 앞블록 bp로가서 그 헤더에 적힌 크기+뒤블록 bp로가서 그 푸터에 적힌크기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp); // 내 헤더는 그대로라 NEXT_BLKP는 여전히 뒤 블록
    }
#if FIT_POLICY == NEXT_FIT // rover= 지난번 탐색이 멈춤 블록의 bp를 기억해두는 전역 변수
    // 탐색을 rover에서 시작 맞는 블록을 찾으면 rover가 그 블록에 멈춘채로 끝남 그래서 rover는 보통 말록으로 내준 블록을 가르키고있음
    //  만약 (rover가 합친 블록 시작보다 뒤에 있고) 그리고 (rover가 합친 블록 끝보다 앞에 있으면): rover를 합친 블록 시작으로 옮긴다
    if (rover > (char *)bp && rover < NEXT_BLKP(bp))
        rover = bp;

#endif
    insert_free(bp);
    return bp;
}
// 블록 크기를 바꿈 새 블록을 말록->기존 데이터 복사->기존 블록 free
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    if (ptr == NULL) // ptr이 NULL이면 그냥 말록과 같다
        return mm_malloc(size);

    if (size == 0) // 사이즈가0이면 그냥 free와 같다
    {
        mm_free(ptr);
        return NULL;
    }

    newptr = mm_malloc(size); // 새블록 할당 실패시 기존블록은 그대로 둔다
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE; // 복사할 크기=기존블록의 플레이로드 크기  블록 전체 크기 - 헤더(4) - 풋터(4) = 블록 크기 - 8 예) 기존 블록 24 → payload 16
    if (size < copySize)                       // 줄이는 경우엔 새 크기만큼 복사 예) payload 16, 새 size 10 → 10바이트만 복사
        copySize = size;
    memcpy(newptr, oldptr, copySize); // 데이터 복사후 기존 블록 반납
    mm_free(oldptr);
    return newptr;
}
