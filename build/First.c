// This is HVM's C runtime template. HVM files generate a copy of this file,
// modified to also include user-defined rules. It then can be compiled to run
// in parallel with -lpthreads.

#include <assert.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

#define PARALLEL

#ifdef PARALLEL
#include <pthread.h>
#include <stdatomic.h>
#endif

#define LIKELY(x) __builtin_expect((x), 1)
#define UNLIKELY(x) __builtin_expect((x), 0)

// Types
// -----

typedef uint8_t u8;
typedef uint32_t u32;
typedef uint64_t u64;

#ifdef PARALLEL
typedef pthread_t Thd;
#endif

// Consts
// ------

#define U64_PER_KB (0x80)
#define U64_PER_MB (0x20000)
#define U64_PER_GB (0x8000000)

// HVM pointers can address a 2^32 space of 64-bit elements, so, when the
// program starts, we pre-alloc the maximum addressable heap, 32 GB. This will
// be replaced by a proper arena allocator soon (see the Issues)!
#define HEAP_SIZE (8 * U64_PER_GB * sizeof(u64))

#ifdef PARALLEL
#define MAX_WORKERS (12)
#else
#define MAX_WORKERS (1)
#endif

#define MAX_DUPS (16777216)
#define MAX_DYNFUNS (65536)
#define MAX_ARITY (16)

// Each worker has a fraction of the total.
#define MEM_SPACE (HEAP_SIZE/sizeof(u64)/MAX_WORKERS)
#define NORMAL_SEEN_MCAP (HEAP_SIZE/sizeof(u64)/(sizeof(u64)*8))

// Max different colors we're able to readback
#define DIRS_MCAP (0x10000)

// Terms
// -----
// HVM's runtime stores terms in a 64-bit memory. Each element is a Link, which
// usually points to a constructor. It stores a Tag representing the ctor's
// variant, and possibly a position on the memory. So, for example, `Lnk ptr =
// APP * TAG | 137` creates a pointer to an app node stored on position 137.
// Some links deal with variables: DP0, DP1, VAR, ARG and ERA.  The OP2 link
// represents a numeric operation, and U32 and F32 links represent unboxed nums.

typedef u64 Lnk;

#define VAL ((u64) 1)
#define EXT ((u64) 0x100000000)
#define ARI ((u64) 0x100000000000000)
#define TAG ((u64) 0x1000000000000000)

#define DP0 (0x0) // points to the dup node that binds this variable (left side)
#define DP1 (0x1) // points to the dup node that binds this variable (right side)
#define VAR (0x2) // points to the λ that binds this variable
#define ARG (0x3) // points to the occurrence of a bound variable a linear argument
#define ERA (0x4) // signals that a binder doesn't use its bound variable
#define LAM (0x5) // arity = 2
#define APP (0x6) // arity = 2
#define PAR (0x7) // arity = 2 // TODO: rename to SUP
#define CTR (0x8) // arity = user defined
#define CAL (0x9) // arity = user defined
#define OP2 (0xA) // arity = 2
#define U32 (0xB) // arity = 0 (unboxed)
#define F32 (0xC) // arity = 0 (unboxed)
#define NIL (0xF) // not used

#define ADD (0x0)
#define SUB (0x1)
#define MUL (0x2)
#define DIV (0x3)
#define MOD (0x4)
#define AND (0x5)
#define OR  (0x6)
#define XOR (0x7)
#define SHL (0x8)
#define SHR (0x9)
#define LTN (0xA)
#define LTE (0xB)
#define EQL (0xC)
#define GTE (0xD)
#define GTN (0xE)
#define NEQ (0xF)

//GENERATED_CONSTRUCTOR_IDS_START//
#define _LESS__1_ (145)
#define _INSERT__SPLIT__M__12_ (185)
#define _JUST__1_ (140)
#define _LOOKUP__0_ (294)
#define _LT__2_ (238)
#define _X5BX5DX2DX2264__0_ (252)
#define _FROMLIST__2_ (290)
#define _LOOKUP__K__9_ (17)
#define _EQUAL__1_ (131)
#define _FLATTEN__1_ (263)
#define _ORD_CONSTRUCTOR__2_ (288)
#define _Z__X2264____0_ (130)
#define _INSERT__5_ (147)
#define _ORD_CONSTRUCTOR__0_ (152)
#define _SORT__0_ (217)
#define _X5BX5D__0_ (21)
#define _INSERT__0_ (262)
#define _MAPMAYBE__0_ (276)
#define _X2264X2DSUC__2_ (63)
#define _HERE__4_ (37)
#define _X5B__X5D__1_ (77)
#define _X2264X2DANTISYM__0_ (4)
#define _MAPINL__0_ (115)
#define _IT__2_ (12)
#define _XAC____0_ (28)
#define _ORDX2DX5BX5DX221E__2_ (68)
#define _MAPMAYBE__SPLIT__D__4_ (178)
#define _SUBST__4_ (278)
#define _X5BX5DX2DX2264__3_ (106)
#define _TDOX2DNAT__0_ (112)
#define _TESTFROMLIST__0_ (116)
#define _X5BX5DX221EX2DTRANS__7_ (47)
#define _X2264X2DREFL__SPLIT__A__1_ (38)
#define _X2264X2DTRANS__1_ (102)
#define _EQUAL__2_ (187)
#define _X2264X2DSUC__1_ (81)
#define _LOOKUP__3_ (216)
#define _Z__X2237____0_ (226)
#define _X5BX5DX221EX2DTRANS__H__7_ (210)
#define _FALSE__0_ (283)
#define _SORT__3_ (80)
#define _X5BX5DX221EX2DTRANS__0_ (244)
#define _X2264X2DTRANS__SPLIT__A__1_ (103)
#define _X5BX5DX221EX2DREFL__0_ (10)
#define _TRINAT__SPLIT__B__3_ (198)
#define _TRUE__0_ (202)
#define _MAPINL__1_ (15)
#define _ORDX2DX5BX5DX221E__1_ (267)
#define _MAPINR__2_ (93)
#define _LEAF__1_ (48)
#define _MAPINL__4_ (124)
#define _INR__0_ (146)
#define _X2264X2DTRANS__SPLIT__D__5_ (175)
#define _X5BX5DX2DX2264X2DI__4_ (87)
#define _X5BX5DX221EX2DTRANS__SPLIT__F__8_ (211)
#define _X5BX5DX221EX2DTRANS__4_ (221)
#define _TEST1__0_ (166)
#define _X2BX221EX2DX2264X2DI__0_ (154)
#define _TRINAT__E__4_ (200)
#define _NOTHING__0_ (259)
#define _X5BX5DX221EX2DTRANS__SPLIT__C__11_ (223)
#define _SUBST__1_ (230)
#define _X2264X2DDEC__2_ (57)
#define _SUBST__2_ (2)
#define _Z__X2265____0_ (170)
#define _X2BX221E__0_ (61)
#define _FLATTEN__SPLIT__E__5_ (183)
#define _X2264X2DTRANS__2_ (225)
#define _LOOKUP__4_ (287)
#define _Z__X2BX2B____SPLIT__B__3_ (208)
#define _FST__1_ (55)
#define _MAPMAYBE__2_ (273)
#define _INSERT__7_ (6)
#define _TRINAT__SPLIT__B__2_ (150)
#define _LOOKUP__SPLIT__F__6_ (123)
#define _MONUS__SPLIT__3_ (176)
#define _X2DX221EX2DX2264__0_ (206)
#define _LEFT__4_ (51)
#define _INSERT__SPLIT__F__8_ (229)
#define _SORT__1_ (79)
#define _IT__1_ (119)
#define _X5BX5DX221EX2DTRANS__SPLIT__E__16_ (213)
#define _TDO_CONSTRUCTOR__1_ (234)
#define _REFL__0_ (292)
#define _X2BX221EX2DX2264X2DI__1_ (13)
#define _HERE__0_ (36)
#define _X5BX5DX221EX2DTRANS__6_ (241)
#define _Z__X2C____2_ (126)
#define _HERE__3_ (181)
#define _NODE__3_ (45)
#define _TRINAT__SPLIT__E__5_ (201)
#define _ORDX2DX5BX5DX221E__0_ (254)
#define _NODE__1_ (127)
#define _LESS__2_ (66)
#define _SUC__0_ (128)
#define _X2BX221EX2DX2264__1_ (75)
#define _TRINAT__D__3_ (199)
#define _CONG__0_ (203)
#define _X2264X2DDEC__SPLIT__A__3_ (268)
#define _IF__3_ (31)
#define _ORD_CONSTRUCTOR__1_ (162)
#define _MAPMAYBE__4_ (65)
#define _GT__2_ (279)
#define _MAPINR__5_ (94)
#define _MAPMAYBE__3_ (151)
#define _X2264X2DDEC__1_ (186)
#define _X5BX5DX221EX2DREFL__SPLIT__C__3_ (172)
#define _X5BX5DX2DX2264X2DI__3_ (86)
#define _INSERT__M__11_ (285)
#define _X5BX5DX221EX2DANTISYM__0_ (135)
#define _FLATTEN__4_ (274)
#define _FROMLIST__3_ (117)
#define _NODE__0_ (44)
#define _Z__X2C____0_ (125)
#define _MAPINR__3_ (207)
#define _EQUAL__3_ (9)
#define _TRINAT__SPLIT__A__2_ (53)
#define _IT__0_ (257)
#define _LOOKUP__5_ (264)
#define _X2DX221EX2DX2264X2DI__0_ (26)
#define _FLATTEN__5_ (121)
#define _X5BX5DX221EX2DTRANS__SPLIT__G__13_ (25)
#define _X2DX221EX2DX2264__1_ (114)
#define _INSERT__3_ (233)
#define _X5BX5DX2DX2264X2DI__2_ (281)
#define _ORDX2DA__0_ (269)
#define _TDO_CONSTRUCTOR__2_ (165)
#define _MAPINL__5_ (16)
#define _INSERT__8_ (7)
#define _X5BX5DX221EX2DREFL__2_ (59)
#define _SO__0_ (256)
#define _INL__0_ (0)
#define _ZERO__0_ (167)
#define _X2264X2DSUC__3_ (41)
#define _JUST__0_ (255)
#define _INR__1_ (91)
#define _GREATER__2_ (104)
#define _MAPINR__SPLIT__E__5_ (88)
#define _SND__SPLIT__A__1_ (190)
#define _SUBST__3_ (236)
#define _MAPINR__1_ (143)
#define _NODE__2_ (243)
#define _X2DX221EX2DX2264X2DI__1_ (30)
#define _GREATER__3_ (105)
#define _X2264X2DZERO__0_ (258)
#define _FROMLIST__0_ (247)
#define _X2264X2DTRANS__5_ (96)
#define _FROMLIST__SPLIT__C__3_ (242)
#define _X5BX5DX2DX2264X2DI__0_ (289)
#define _X2264X2DZERO__1_ (39)
#define _ORD_CONSTRUCTOR__4_ (71)
#define _EQ__2_ (272)
#define _MAPINL__SPLIT__E__5_ (144)
#define _TRINAT__C__2_ (188)
#define _SND__1_ (158)
#define _TESTFLATTEN__0_ (280)
#define _LEFT__2_ (50)
#define _X5B__X5D__0_ (76)
#define _INL__1_ (1)
#define _LOOKUP__2_ (19)
#define _X2BX221EX2DX2264X2DI__2_ (14)
#define _Z__X2237____2_ (118)
#define _TESTLOOKUP__0_ (163)
#define _MAPINR__4_ (271)
#define _EQ__SPLIT__1_ (85)
#define _MAPINL__3_ (284)
#define _LOOKUP__SPLIT__K__10_ (136)
#define _FROMLIST__1_ (193)
#define _HERE__2_ (132)
#define _HERE__1_ (215)
#define _X2264X2DTRANS__4_ (95)
#define _X2264X2DREFL__B__1_ (40)
#define _SYM__0_ (171)
#define _X5BX5DX221EX2DTRANS__1_ (46)
#define _ORDX2DX5BX5DX221E__3_ (69)
#define _LESS__0_ (122)
#define _TRINAT__2_ (52)
#define _ORDX2DNAT__0_ (70)
#define _MONUS__2_ (192)
#define _X5BX5DX221EX2DTRANS__5_ (78)
#define _GT__SPLIT__1_ (235)
#define _ORD_CONSTRUCTOR__3_ (194)
#define _RIGHT__4_ (35)
#define _RIGHT__2_ (97)
#define _SND__0_ (157)
#define _FST__SPLIT__A__1_ (56)
#define _X5BX5DX221EX2DREFL__3_ (11)
#define _X2DX221EX2DX2264X2DI__2_ (27)
#define _SUBST__5_ (251)
#define _X2264X2DDEC__3_ (58)
#define _TRI__SPLIT__A__1_ (108)
#define _X5BX5DX2DX2264__1_ (209)
#define _X2264X2DTRANS__0_ (261)
#define _X2264X2DREFL__1_ (42)
#define _GREATER__0_ (250)
#define _LOOKUP__6_ (20)
#define _TRINAT__0_ (148)
#define _X5BX5DX221EX2DTRANS__2_ (99)
#define _ORDX2DX22A4__0_ (149)
#define _INSERT__2_ (231)
#define _LEAF__0_ (98)
#define _INSERT__4_ (92)
#define _SUBST__6_ (3)
#define _TESTINSERT__0_ (111)
#define _LOOKUP__1_ (60)
#define _MAPINL__2_ (29)
#define _MAIN_ (82)
#define _X5BX5DX221EX2DREFL__1_ (177)
#define _SUBST__0_ (275)
#define _MAPINR__0_ (189)
#define _RIGHT__1_ (159)
#define _SORT__2_ (134)
#define _FLATTEN__3_ (204)
#define _TRI__0_ (245)
#define _X2264X2DTRANS__3_ (72)
#define _FST__0_ (164)
#define _Z__X2BX2B____3_ (161)
#define _TRINAT__1_ (110)
#define _X2264X2DTRANS__SPLIT__E__8_ (155)
#define _TT__0_ (100)
#define _X5BX5DX221EX2DTRANS__SPLIT__D__12_ (23)
#define _Z__X2BX2B____0_ (160)
#define _RIGHT__0_ (34)
#define _LEFT__0_ (237)
#define _LT__SPLIT__1_ (239)
#define _Z__X2BX2B____2_ (282)
#define _INSERT__1_ (270)
#define _TDO_CONSTRUCTOR__0_ (195)
#define _Z__X2C____1_ (196)
#define _ORDX2DA__SPLIT__A__1_ (224)
#define _EQUAL__0_ (8)
#define _X5BX5DX2DX2264__2_ (153)
#define _MAPMAYBE__1_ (64)
#define _GREATER__1_ (205)
#define _X2264X2DDEC__D__3_ (142)
#define _TESTMAPMAYBE__0_ (197)
#define _LEFT__3_ (138)
#define _FLATTEN__0_ (182)
#define _ORDX2DA__1_ (253)
#define _TRI__1_ (246)
#define _Z__X2BX2B____1_ (240)
#define _X2264X2DDEC__0_ (265)
#define _TESTTRINAT__0_ (228)
#define _SUC__1_ (129)
#define _Z__X2237____1_ (248)
#define _TRANS__0_ (266)
#define _X2264X2DREFL__0_ (133)
#define _LESS__3_ (67)
#define _LEFT__1_ (84)
#define _X5BX5DX221EX2DTRANS__3_ (286)
#define _RIGHT__3_ (73)
#define _MAIN__0_ (83)
#define _X2BX221EX2DX2264__0_ (74)
#define _X2DX221E__0_ (212)
#define _FLATTEN__2_ (120)
#define _TESTBST__0_ (113)
#define _INSERT__6_ (227)
#define _X2264X2DSUC__0_ (232)
#define _X5BX5DX2DX2264X2DI__1_ (169)

//GENERATED_CONSTRUCTOR_IDS_END//

#ifndef _MAIN_
#define _MAIN_ (0)
#endif

// Threads
// -------

typedef struct {
  u64 size;
  u64* data;
} Arr;

typedef struct {
  u64* data;
  u64  size;
  u64  mcap;
} Stk;

typedef struct {
  u64  tid;
  Lnk* node;
  u64  size;
  Stk  free[MAX_ARITY];
  u64  cost;
  u64  dups;

  #ifdef PARALLEL
  u64             has_work;
  pthread_mutex_t has_work_mutex;
  pthread_cond_t  has_work_signal;

  u64             has_result;
  pthread_mutex_t has_result_mutex;
  pthread_cond_t  has_result_signal;

  Thd  thread;
  #endif
} Worker;

// Globals
// -------

Worker workers[MAX_WORKERS];

// Array
// -----
// Some array utils

void array_write(Arr* arr, u64 idx, u64 value) {
  arr->data[idx] = value;
}

u64 array_read(Arr* arr, u64 idx) {
  return arr->data[idx];
}

// Stack
// -----
// Some stack utils.

u64 stk_growth_factor = 16;

void stk_init(Stk* stack) {
  stack->size = 0;
  stack->mcap = stk_growth_factor;
  stack->data = malloc(stack->mcap * sizeof(u64));
  assert(stack->data);
}

void stk_free(Stk* stack) {
  free(stack->data);
}

void stk_push(Stk* stack, u64 val) {
  if (UNLIKELY(stack->size == stack->mcap)) {
    stack->mcap = stack->mcap * stk_growth_factor;
    stack->data = realloc(stack->data, stack->mcap * sizeof(u64));
  }
  stack->data[stack->size++] = val;
}

u64 stk_pop(Stk* stack) {
  if (LIKELY(stack->size > 0)) {
    // TODO: shrink? -- impacts performance considerably
    //if (stack->size == stack->mcap / stk_growth_factor) {
      //stack->mcap = stack->mcap / stk_growth_factor;
      //stack->data = realloc(stack->data, stack->mcap * sizeof(u64));
      //printf("shrink %llu\n", stack->mcap);
    //}
    return stack->data[--stack->size];
  } else {
    return -1;
  }
}

u64 stk_find(Stk* stk, u64 val) {
  for (u64 i = 0; i < stk->size; ++i) {
    if (stk->data[i] == val) {
      return i;
    }
  }
  return -1;
}

// Memory
// ------
// Creating, storing and reading Lnks, allocating and freeing memory.

Lnk Var(u64 pos) {
  return (VAR * TAG) | pos;
}

Lnk Dp0(u64 col, u64 pos) {
  return (DP0 * TAG) | (col * EXT) | pos;
}

Lnk Dp1(u64 col, u64 pos) {
  return (DP1 * TAG) | (col * EXT) | pos;
}

Lnk Arg(u64 pos) {
  return (ARG * TAG) | pos;
}

Lnk Era(void) {
  return (ERA * TAG);
}

Lnk Lam(u64 pos) {
  return (LAM * TAG) | pos;
}

Lnk App(u64 pos) {
  return (APP * TAG) | pos;
}

Lnk Par(u64 col, u64 pos) {
  return (PAR * TAG) | (col * EXT) | pos;
}

Lnk Op2(u64 ope, u64 pos) {
  return (OP2 * TAG) | (ope * EXT) | pos;
}

Lnk U_32(u64 val) {
  return (U32 * TAG) | val;
}

Lnk Nil(void) {
  return NIL * TAG;
}

Lnk Ctr(u64 ari, u64 fun, u64 pos) {
  return (CTR * TAG) | (ari * ARI) | (fun * EXT) | pos;
}

Lnk Cal(u64 ari, u64 fun, u64 pos) {
  return (CAL * TAG) | (ari * ARI) | (fun * EXT) | pos;
}

u64 get_tag(Lnk lnk) {
  return lnk / TAG;
}

u64 get_ext(Lnk lnk) {
  return (lnk / EXT) & 0xFFFFFF;
}

u64 get_val(Lnk lnk) {
  return lnk & 0xFFFFFFFF;
}

u64 get_ari(Lnk lnk) {
  return (lnk / ARI) & 0xF;
}

u64 get_loc(Lnk lnk, u64 arg) {
  return get_val(lnk) + arg;
}

// Dereferences a Lnk, getting what is stored on its target position
Lnk ask_lnk(Worker* mem, u64 loc) {
  return mem->node[loc];
}

// Dereferences the nth argument of the Term represented by this Lnk
Lnk ask_arg(Worker* mem, Lnk term, u64 arg) {
  return ask_lnk(mem, get_loc(term, arg));
}

// This inserts a value in another. It just writes a position in memory if
// `value` is a constructor. If it is VAR, DP0 or DP1, it also updates the
// corresponding λ or dup binder.
u64 link(Worker* mem, u64 loc, Lnk lnk) {
  mem->node[loc] = lnk;
  //array_write(mem->nodes, loc, lnk);
  if (get_tag(lnk) <= VAR) {
    mem->node[get_loc(lnk, get_tag(lnk) == DP1 ? 1 : 0)] = Arg(loc);
    //array_write(mem->nodes, get_loc(lnk, get_tag(lnk) == DP1 ? 1 : 0), Arg(loc));
  }
  return lnk;
}

// Allocates a block of memory, up to 16 words long
u64 alloc(Worker* mem, u64 size) {
  if (UNLIKELY(size == 0)) {
    return 0;
  } else {
    u64 reuse = stk_pop(&mem->free[size]);
    if (reuse != -1) {
      return reuse;
    }
    u64 loc = mem->size;
    mem->size += size;
    return mem->tid * MEM_SPACE + loc;
    //return __atomic_fetch_add(&mem->nodes->size, size, __ATOMIC_RELAXED);
  }
}

// Frees a block of memory by adding its position a freelist
void clear(Worker* mem, u64 loc, u64 size) {
  stk_push(&mem->free[size], loc);
}

// Garbage Collection
// ------------------

// This clears the memory used by a term that becames unreachable. It just frees
// all its nodes recursivelly. This is called as soon as a term goes out of
// scope. No global GC pass is necessary to find unreachable terms!
// HVM can still produce some garbage in very uncommon situations that are
// mostly irrelevant in practice. Absolute GC-freedom, though, requires
// uncommenting the `reduce` lines below, but this would make HVM not 100% lazy
// in some cases, so it should be called in a separate thread.
void collect(Worker* mem, Lnk term) {
  switch (get_tag(term)) {
    case DP0: {
      link(mem, get_loc(term,0), Era());
      //reduce(mem, get_loc(ask_arg(mem,term,1),0));
      break;
    }
    case DP1: {
      link(mem, get_loc(term,1), Era());
      //reduce(mem, get_loc(ask_arg(mem,term,0),0));
      break;
    }
    case VAR: {
      link(mem, get_loc(term,0), Era());
      break;
    }
    case LAM: {
      if (get_tag(ask_arg(mem,term,0)) != ERA) {
        link(mem, get_loc(ask_arg(mem,term,0),0), Era());
      }
      collect(mem, ask_arg(mem,term,1));
      clear(mem, get_loc(term,0), 2);
      break;
    }
    case APP: {
      collect(mem, ask_arg(mem,term,0));
      collect(mem, ask_arg(mem,term,1));
      clear(mem, get_loc(term,0), 2);
      break;
    }
    case PAR: {
      collect(mem, ask_arg(mem,term,0));
      collect(mem, ask_arg(mem,term,1));
      clear(mem, get_loc(term,0), 2);
      break;
    }
    case OP2: {
      collect(mem, ask_arg(mem,term,0));
      collect(mem, ask_arg(mem,term,1));
      clear(mem, get_loc(term,0), 2);
      break;
    }
    case U32: {
      break;
    }
    case CTR: case CAL: {
      u64 arity = get_ari(term);
      for (u64 i = 0; i < arity; ++i) {
        collect(mem, ask_arg(mem,term,i));
      }
      clear(mem, get_loc(term,0), arity);
      break;
    }
  }
}

// Terms
// -----

void inc_cost(Worker* mem) {
  mem->cost++;
}

u64 gen_dupk(Worker* mem) {
  return mem->dups++ & 0xFFFFFF;
}

// Performs a `x <- value` substitution. It just calls link if the substituted
// value is a term. If it is an ERA node, that means `value` is now unreachable,
// so we just call the collector.
void subst(Worker* mem, Lnk lnk, Lnk val) {
  if (get_tag(lnk) != ERA) {
    link(mem, get_loc(lnk,0), val);
  } else {
    collect(mem, val);
  }
}

// (F {a0 a1} b c ...)
// ------------------- CAL-PAR
// dup b0 b1 = b
// dup c0 c1 = c
// ...
// {(F a0 b0 c0 ...) (F a1 b1 c1 ...)}
Lnk cal_par(Worker* mem, u64 host, Lnk term, Lnk argn, u64 n) {
  inc_cost(mem);
  u64 arit = get_ari(term);
  u64 func = get_ext(term);
  u64 fun0 = get_loc(term, 0);
  u64 fun1 = alloc(mem, arit);
  u64 par0 = get_loc(argn, 0);
  for (u64 i = 0; i < arit; ++i) {
    if (i != n) {
      u64 leti = alloc(mem, 3);
      u64 argi = ask_arg(mem, term, i);
      link(mem, fun0+i, Dp0(get_ext(argn), leti));
      link(mem, fun1+i, Dp1(get_ext(argn), leti));
      link(mem, leti+2, argi);
    } else {
      link(mem, fun0+i, ask_arg(mem, argn, 0));
      link(mem, fun1+i, ask_arg(mem, argn, 1));
    }
  }
  link(mem, par0+0, Cal(arit, func, fun0));
  link(mem, par0+1, Cal(arit, func, fun1));
  u64 done = Par(get_ext(argn), par0);
  link(mem, host, done);
  return done;
}

// Reduces a term to weak head normal form.
Lnk reduce(Worker* mem, u64 root, u64 slen) {
  Stk stack;
  stk_init(&stack);

  u64 init = 1;
  u32 host = (u32)root;

  while (1) {

    u64 term = ask_lnk(mem, host);

    //printf("reduce "); debug_print_lnk(term); printf("\n");
    //printf("------\n");
    //printf("reducing: host=%d size=%llu init=%llu ", host, stack.size, init); debug_print_lnk(term); printf("\n");
    //for (u64 i = 0; i < 256; ++i) {
      //printf("- %llx ", i); debug_print_lnk(mem->node[i]); printf("\n");
    //}

    if (init == 1) {
      switch (get_tag(term)) {
        case APP: {
          stk_push(&stack, host);
          //stack[size++] = host;
          init = 1;
          host = get_loc(term, 0);
          continue;
        }
        case DP0:
        case DP1: {
          #ifdef PARALLEL
          // TODO: reason about this, comment
          atomic_flag* flag = ((atomic_flag*)(mem->node + get_loc(term,0))) + 6;
          if (atomic_flag_test_and_set(flag) != 0) {
            continue;
          }
          #endif
          stk_push(&stack, host);
          host = get_loc(term, 2);
          continue;
        }
        case OP2: {
          if (slen == 1 || stack.size > 0) {
            stk_push(&stack, host);
            stk_push(&stack, get_loc(term, 0) | 0x80000000);
            //stack[size++] = host;
            //stack[size++] = get_loc(term, 0) | 0x80000000;
            host = get_loc(term, 1);
            continue;
          }
          break;
        }
        case CAL: {
          u64 fun = get_ext(term);
          u64 ari = get_ari(term);

          switch (fun)
          //GENERATED_REWRITE_RULES_STEP_0_START//
          {
            case _LESS__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _INSERT__SPLIT__M__12_: {
              if (get_ari(term) == 12) {
                stk_push(&stack, host);
                host = get_loc(term, 11);
                continue;
              }
            };
            case _JUST__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LT__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX2DX2264__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FROMLIST__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__K__9_: {
              if (get_ari(term) == 9) {
                init = 0;
                continue;
              }
            };
            case _EQUAL__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _FLATTEN__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _ORD_CONSTRUCTOR__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _Z__X2264____0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _INSERT__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _ORD_CONSTRUCTOR__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _SORT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5D__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _INSERT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAPMAYBE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DSUC__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _HERE__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _X5B__X5D__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DANTISYM__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAPINL__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _IT__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _XAC____0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _ORDX2DX5BX5DX221E__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _MAPMAYBE__SPLIT__D__4_: {
              if (get_ari(term) == 4) {
                stk_push(&stack, host);
                host = get_loc(term, 3);
                continue;
              }
            };
            case _SUBST__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX2DX2264__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _TDOX2DNAT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _TESTFROMLIST__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__7_: {
              if (get_ari(term) == 7) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DREFL__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _X2264X2DTRANS__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _EQUAL__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DSUC__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _Z__X2237____0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__H__7_: {
              if (get_ari(term) == 7) {
                init = 0;
                continue;
              }
            };
            case _FALSE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _SORT__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DTRANS__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _X5BX5DX221EX2DREFL__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__SPLIT__B__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 1);
                continue;
              }
            };
            case _TRUE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAPINL__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _ORDX2DX5BX5DX221E__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _MAPINR__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _LEAF__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _MAPINL__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _INR__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DTRANS__SPLIT__D__5_: {
              if (get_ari(term) == 5) {
                stk_push(&stack, host);
                host = get_loc(term, 3);
                continue;
              }
            };
            case _X5BX5DX2DX2264X2DI__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__F__8_: {
              if (get_ari(term) == 8) {
                stk_push(&stack, host);
                host = get_loc(term, 5);
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _TEST1__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2BX221EX2DX2264X2DI__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__E__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _NOTHING__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__C__11_: {
              if (get_ari(term) == 11) {
                stk_push(&stack, host);
                host = get_loc(term, 2);
                continue;
              }
            };
            case _SUBST__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DDEC__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _SUBST__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _Z__X2265____0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2BX221E__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FLATTEN__SPLIT__E__5_: {
              if (get_ari(term) == 5) {
                stk_push(&stack, host);
                host = get_loc(term, 4);
                continue;
              }
            };
            case _X2264X2DTRANS__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _Z__X2BX2B____SPLIT__B__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 1);
                continue;
              }
            };
            case _FST__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _MAPMAYBE__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _INSERT__7_: {
              if (get_ari(term) == 7) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__SPLIT__B__2_: {
              if (get_ari(term) == 2) {
                stk_push(&stack, host);
                host = get_loc(term, 1);
                continue;
              }
            };
            case _LOOKUP__SPLIT__F__6_: {
              if (get_ari(term) == 6) {
                stk_push(&stack, host);
                host = get_loc(term, 5);
                continue;
              }
            };
            case _MONUS__SPLIT__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _X2DX221EX2DX2264__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LEFT__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _INSERT__SPLIT__F__8_: {
              if (get_ari(term) == 8) {
                stk_push(&stack, host);
                host = get_loc(term, 5);
                continue;
              }
            };
            case _SORT__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _IT__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__E__16_: {
              if (get_ari(term) == 16) {
                stk_push(&stack, host);
                host = get_loc(term, 4);
                continue;
              }
            };
            case _TDO_CONSTRUCTOR__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _REFL__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2BX221EX2DX2264X2DI__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _HERE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__6_: {
              if (get_ari(term) == 6) {
                init = 0;
                continue;
              }
            };
            case _Z__X2C____2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _HERE__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _NODE__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__SPLIT__E__5_: {
              if (get_ari(term) == 5) {
                stk_push(&stack, host);
                host = get_loc(term, 4);
                continue;
              }
            };
            case _ORDX2DX5BX5DX221E__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _NODE__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _LESS__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _SUC__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2BX221EX2DX2264__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__D__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _CONG__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DDEC__SPLIT__A__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _IF__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _ORD_CONSTRUCTOR__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _MAPMAYBE__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _GT__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _MAPINR__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _MAPMAYBE__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DDEC__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DREFL__SPLIT__C__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 2);
                continue;
              }
            };
            case _X5BX5DX2DX2264X2DI__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _INSERT__M__11_: {
              if (get_ari(term) == 11) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DANTISYM__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FLATTEN__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _FROMLIST__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _NODE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _Z__X2C____0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAPINR__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _EQUAL__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__SPLIT__A__2_: {
              if (get_ari(term) == 2) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _IT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _X2DX221EX2DX2264X2DI__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FLATTEN__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__G__13_: {
              if (get_ari(term) == 13) {
                stk_push(&stack, host);
                host = get_loc(term, 6);
                continue;
              }
            };
            case _X2DX221EX2DX2264__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _INSERT__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX2DX2264X2DI__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _ORDX2DA__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _TDO_CONSTRUCTOR__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _MAPINL__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _INSERT__8_: {
              if (get_ari(term) == 8) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DREFL__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _SO__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _INL__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _ZERO__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DSUC__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _JUST__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _INR__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _GREATER__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _MAPINR__SPLIT__E__5_: {
              if (get_ari(term) == 5) {
                stk_push(&stack, host);
                host = get_loc(term, 4);
                continue;
              }
            };
            case _SND__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _SUBST__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _MAPINR__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _NODE__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _X2DX221EX2DX2264X2DI__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _GREATER__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DZERO__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FROMLIST__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DTRANS__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _FROMLIST__SPLIT__C__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 2);
                continue;
              }
            };
            case _X5BX5DX2DX2264X2DI__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DZERO__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _ORD_CONSTRUCTOR__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _EQ__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _MAPINL__SPLIT__E__5_: {
              if (get_ari(term) == 5) {
                stk_push(&stack, host);
                host = get_loc(term, 4);
                continue;
              }
            };
            case _TRINAT__C__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _SND__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TESTFLATTEN__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LEFT__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _X5B__X5D__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _INL__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _X2BX221EX2DX2264X2DI__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _Z__X2237____2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _TESTLOOKUP__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAPINR__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _EQ__SPLIT__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _MAPINL__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__SPLIT__K__10_: {
              if (get_ari(term) == 10) {
                stk_push(&stack, host);
                host = get_loc(term, 9);
                continue;
              }
            };
            case _FROMLIST__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _HERE__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _HERE__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DTRANS__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DREFL__B__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _SYM__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _ORDX2DX5BX5DX221E__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _LESS__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _ORDX2DNAT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MONUS__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _GT__SPLIT__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _ORD_CONSTRUCTOR__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _RIGHT__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _RIGHT__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _SND__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FST__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _X5BX5DX221EX2DREFL__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _X2DX221EX2DX2264X2DI__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _SUBST__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DDEC__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _TRI__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _X5BX5DX2DX2264__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DTRANS__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DREFL__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _GREATER__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__6_: {
              if (get_ari(term) == 6) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _ORDX2DX22A4__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _INSERT__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _LEAF__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _INSERT__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _SUBST__6_: {
              if (get_ari(term) == 6) {
                init = 0;
                continue;
              }
            };
            case _TESTINSERT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LOOKUP__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _MAPINL__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _MAIN_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DREFL__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _SUBST__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAPINR__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _RIGHT__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _SORT__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _FLATTEN__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _TRI__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DTRANS__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _FST__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _Z__X2BX2B____3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _TRINAT__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DTRANS__SPLIT__E__8_: {
              if (get_ari(term) == 8) {
                stk_push(&stack, host);
                host = get_loc(term, 4);
                continue;
              }
            };
            case _TT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__D__12_: {
              if (get_ari(term) == 12) {
                stk_push(&stack, host);
                host = get_loc(term, 3);
                continue;
              }
            };
            case _Z__X2BX2B____0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _RIGHT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LEFT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LT__SPLIT__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _Z__X2BX2B____2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _INSERT__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TDO_CONSTRUCTOR__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _Z__X2C____1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _ORDX2DA__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _EQUAL__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX2DX2264__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _MAPMAYBE__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _GREATER__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DDEC__D__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _TESTMAPMAYBE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LEFT__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _FLATTEN__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _ORDX2DA__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TRI__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _Z__X2BX2B____1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DDEC__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _TESTTRINAT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _SUC__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _Z__X2237____1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TRANS__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DREFL__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LESS__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _LEFT__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX221EX2DTRANS__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _RIGHT__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _MAIN__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2BX221EX2DX2264__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X2DX221E__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FLATTEN__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _TESTBST__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _INSERT__6_: {
              if (get_ari(term) == 6) {
                init = 0;
                continue;
              }
            };
            case _X2264X2DSUC__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _X5BX5DX2DX2264X2DI__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };

          }
          //GENERATED_REWRITE_RULES_STEP_0_END//

          break;
        }
      }

    } else {

      switch (get_tag(term)) {
        case APP: {
          u64 arg0 = ask_arg(mem, term, 0);
          switch (get_tag(arg0)) {

            // (λx(body) a)
            // ------------ APP-LAM
            // x <- a
            // body
            case LAM: {
              //printf("app-lam\n");
              inc_cost(mem);
              subst(mem, ask_arg(mem, arg0, 0), ask_arg(mem, term, 1));
              u64 done = link(mem, host, ask_arg(mem, arg0, 1));
              clear(mem, get_loc(term,0), 2);
              clear(mem, get_loc(arg0,0), 2);
              init = 1;
              continue;
            }

            // ({a b} c)
            // ----------------- APP-PAR
            // dup x0 x1 = c
            // {(a x0) (b x1)}
            case PAR: {
              //printf("app-sup\n");
              inc_cost(mem);
              u64 app0 = get_loc(term, 0);
              u64 app1 = get_loc(arg0, 0);
              u64 let0 = alloc(mem, 3);
              u64 par0 = alloc(mem, 2);
              link(mem, let0+2, ask_arg(mem, term, 1));
              link(mem, app0+1, Dp0(get_ext(arg0), let0));
              link(mem, app0+0, ask_arg(mem, arg0, 0));
              link(mem, app1+0, ask_arg(mem, arg0, 1));
              link(mem, app1+1, Dp1(get_ext(arg0), let0));
              link(mem, par0+0, App(app0));
              link(mem, par0+1, App(app1));
              u64 done = Par(get_ext(arg0), par0);
              link(mem, host, done);
              break;
            }

          }
          break;
        }
        case DP0:
        case DP1: {
          u64 arg0 = ask_arg(mem, term, 2);
          switch (get_tag(arg0)) {

            // dup r s = λx(f)
            // --------------- DUP-LAM
            // dup f0 f1 = f
            // r <- λx0(f0)
            // s <- λx1(f1)
            // x <- {x0 x1}
            case LAM: {
              //printf("dup-lam\n");
              inc_cost(mem);
              u64 let0 = get_loc(term, 0);
              u64 par0 = get_loc(arg0, 0);
              u64 lam0 = alloc(mem, 2);
              u64 lam1 = alloc(mem, 2);
              link(mem, let0+2, ask_arg(mem, arg0, 1));
              link(mem, par0+1, Var(lam1));
              u64 arg0_arg_0 = ask_arg(mem, arg0, 0);
              link(mem, par0+0, Var(lam0));
              subst(mem, arg0_arg_0, Par(get_ext(term), par0));
              u64 term_arg_0 = ask_arg(mem,term,0);
              link(mem, lam0+1, Dp0(get_ext(term), let0));
              subst(mem, term_arg_0, Lam(lam0));
              u64 term_arg_1 = ask_arg(mem,term,1);
              link(mem, lam1+1, Dp1(get_ext(term), let0));
              subst(mem, term_arg_1, Lam(lam1));
              u64 done = Lam(get_tag(term) == DP0 ? lam0 : lam1);
              link(mem, host, done);
              init = 1;
              continue;
            }

            // dup x y = {a b}
            // --------------- DUP-PAR (equal)
            // x <- a
            // y <- b
            //
            // dup x y = {a b}
            // ----------------- DUP-SUP (different)
            // x <- {xA xB}
            // y <- {yA yB}
            // dup xA yA = a
            // dup xB yB = b
            case PAR: {
              //printf("dup-sup\n");
              if (get_ext(term) == get_ext(arg0)) {
                inc_cost(mem);
                subst(mem, ask_arg(mem,term,0), ask_arg(mem,arg0,0));
                subst(mem, ask_arg(mem,term,1), ask_arg(mem,arg0,1));
                u64 done = link(mem, host, ask_arg(mem, arg0, get_tag(term) == DP0 ? 0 : 1));
                clear(mem, get_loc(term,0), 3);
                clear(mem, get_loc(arg0,0), 2);
                init = 1;
                continue;
              } else {
                inc_cost(mem);
                u64 par0 = alloc(mem, 2);
                u64 let0 = get_loc(term,0);
                u64 par1 = get_loc(arg0,0);
                u64 let1 = alloc(mem, 3);
                link(mem, let0+2, ask_arg(mem,arg0,0));
                link(mem, let1+2, ask_arg(mem,arg0,1));
                u64 term_arg_0 = ask_arg(mem,term,0);
                u64 term_arg_1 = ask_arg(mem,term,1);
                link(mem, par1+0, Dp1(get_ext(term),let0));
                link(mem, par1+1, Dp1(get_ext(term),let1));
                link(mem, par0+0, Dp0(get_ext(term),let0));
                link(mem, par0+1, Dp0(get_ext(term),let1));
                subst(mem, term_arg_0, Par(get_ext(arg0),par0));
                subst(mem, term_arg_1, Par(get_ext(arg0),par1));
                u64 done = Par(get_ext(arg0), get_tag(term) == DP0 ? par0 : par1);
                link(mem, host, done);
                break;
              }
              break;
            }

            // dup x y = N
            // ----------- DUP-U32
            // x <- N
            // y <- N
            // ~
            case U32: {
              //printf("dup-u32\n");
              inc_cost(mem);
              subst(mem, ask_arg(mem,term,0), arg0);
              subst(mem, ask_arg(mem,term,1), arg0);
              u64 done = arg0;
              link(mem, host, arg0);
              break;
            }

            // dup x y = (K a b c ...)
            // ----------------------- DUP-CTR
            // dup a0 a1 = a
            // dup b0 b1 = b
            // dup c0 c1 = c
            // ...
            // x <- (K a0 b0 c0 ...)
            // y <- (K a1 b1 c1 ...)
            case CTR: {
              //printf("dup-ctr\n");
              inc_cost(mem);
              u64 func = get_ext(arg0);
              u64 arit = get_ari(arg0);
              if (arit == 0) {
                subst(mem, ask_arg(mem,term,0), Ctr(0, func, 0));
                subst(mem, ask_arg(mem,term,1), Ctr(0, func, 0));
                clear(mem, get_loc(term,0), 3);
                u64 done = link(mem, host, Ctr(0, func, 0));
              } else {
                u64 ctr0 = get_loc(arg0,0);
                u64 ctr1 = alloc(mem, arit);
                for (u64 i = 0; i < arit - 1; ++i) {
                  u64 leti = alloc(mem, 3);
                  link(mem, leti+2, ask_arg(mem, arg0, i));
                  link(mem, ctr0+i, Dp0(get_ext(term), leti));
                  link(mem, ctr1+i, Dp1(get_ext(term), leti));
                }
                u64 leti = get_loc(term, 0);
                link(mem, leti + 2, ask_arg(mem, arg0, arit - 1));
                u64 term_arg_0 = ask_arg(mem, term, 0);
                link(mem, ctr0 + arit - 1, Dp0(get_ext(term), leti));
                subst(mem, term_arg_0, Ctr(arit, func, ctr0));
                u64 term_arg_1 = ask_arg(mem, term, 1);
                link(mem, ctr1 + arit - 1, Dp1(get_ext(term), leti));
                subst(mem, term_arg_1, Ctr(arit, func, ctr1));
                u64 done = Ctr(arit, func, get_tag(term) == DP0 ? ctr0 : ctr1);
                link(mem, host, done);
              }
              break;
            }

            // dup x y = *
            // ----------- DUP-CTR
            // x <- *
            // y <- *
            case ERA: {
              inc_cost(mem);
              subst(mem, ask_arg(mem, term, 0), Era());
              subst(mem, ask_arg(mem, term, 1), Era());
              link(mem, host, Era());
              clear(mem, get_loc(term, 0), 3);
              init = 1;
              continue;
            }

          }
          #ifdef PARALLEL
          atomic_flag* flag = ((atomic_flag*)(mem->node + get_loc(term,0))) + 6;
          atomic_flag_clear(flag);
          #endif
          break;
        }
        case OP2: {
          u64 arg0 = ask_arg(mem, term, 0);
          u64 arg1 = ask_arg(mem, term, 1);

          // (+ a b)
          // --------- OP2-U32
          // add(a, b)
          if (get_tag(arg0) == U32 && get_tag(arg1) == U32) {
            //printf("op2-u32\n");
            inc_cost(mem);
            u64 a = get_val(arg0);
            u64 b = get_val(arg1);
            u64 c = 0;
            switch (get_ext(term)) {
              case ADD: c = (a +  b) & 0xFFFFFFFF; break;
              case SUB: c = (a -  b) & 0xFFFFFFFF; break;
              case MUL: c = (a *  b) & 0xFFFFFFFF; break;
              case DIV: c = (a /  b) & 0xFFFFFFFF; break;
              case MOD: c = (a %  b) & 0xFFFFFFFF; break;
              case AND: c = (a &  b) & 0xFFFFFFFF; break;
              case OR : c = (a |  b) & 0xFFFFFFFF; break;
              case XOR: c = (a ^  b) & 0xFFFFFFFF; break;
              case SHL: c = (a << b) & 0xFFFFFFFF; break;
              case SHR: c = (a >> b) & 0xFFFFFFFF; break;
              case LTN: c = (a <  b) ? 1 : 0;      break;
              case LTE: c = (a <= b) ? 1 : 0;      break;
              case EQL: c = (a == b) ? 1 : 0;      break;
              case GTE: c = (a >= b) ? 1 : 0;      break;
              case GTN: c = (a >  b) ? 1 : 0;      break;
              case NEQ: c = (a != b) ? 1 : 0;      break;
            }
            u64 done = U_32(c);
            clear(mem, get_loc(term,0), 2);
            link(mem, host, done);
          }

          // (+ {a0 a1} b)
          // --------------------- OP2-SUP-0
          // let b0 b1 = b
          // {(+ a0 b0) (+ a1 b1)}
          else if (get_tag(arg0) == PAR) {
            //printf("op2-sup-0\n");
            inc_cost(mem);
            u64 op20 = get_loc(term, 0);
            u64 op21 = get_loc(arg0, 0);
            u64 let0 = alloc(mem, 3);
            u64 par0 = alloc(mem, 2);
            link(mem, let0+2, arg1);
            link(mem, op20+1, Dp0(get_ext(arg0), let0));
            link(mem, op20+0, ask_arg(mem, arg0, 0));
            link(mem, op21+0, ask_arg(mem, arg0, 1));
            link(mem, op21+1, Dp1(get_ext(arg0), let0));
            link(mem, par0+0, Op2(get_ext(term), op20));
            link(mem, par0+1, Op2(get_ext(term), op21));
            u64 done = Par(get_ext(arg0), par0);
            link(mem, host, done);
          }

          // (+ a {b0 b1})
          // --------------- OP2-SUP-1
          // dup a0 a1 = a
          // {(+ a0 b0) (+ a1 b1)}
          else if (get_tag(arg1) == PAR) {
            //printf("op2-sup-1\n");
            inc_cost(mem);
            u64 op20 = get_loc(term, 0);
            u64 op21 = get_loc(arg1, 0);
            u64 let0 = alloc(mem, 3);
            u64 par0 = alloc(mem, 2);
            link(mem, let0+2, arg0);
            link(mem, op20+0, Dp0(get_ext(arg1), let0));
            link(mem, op20+1, ask_arg(mem, arg1, 0));
            link(mem, op21+1, ask_arg(mem, arg1, 1));
            link(mem, op21+0, Dp1(get_ext(arg1), let0));
            link(mem, par0+0, Op2(get_ext(term), op20));
            link(mem, par0+1, Op2(get_ext(term), op21));
            u64 done = Par(get_ext(arg1), par0);
            link(mem, host, done);
          }

          break;
        }
        case CAL: {
          u64 fun = get_ext(term);
          u64 ari = get_ari(term);

          switch (fun)
          //GENERATED_REWRITE_RULES_STEP_1_START//
          {
            case _LESS__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 67, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__SPLIT__M__12_: {
              if (get_tag(ask_arg(mem,term,11)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 11), 11);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 11)) == CTR && get_ext(ask_arg(mem, term, 11)) == 137u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_4));
                link(mem, cal_5 + 2, ask_arg(mem, ask_arg(mem, term, 11), 2));
                u64 cal_6 = alloc(mem, 8);
                link(mem, cal_6 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_6 + 1, ask_arg(mem, term, 1));
                link(mem, cal_6 + 2, Ctr(0, 5, ctr_1));
                link(mem, cal_6 + 3, Ctr(0, 5, ctr_2));
                link(mem, cal_6 + 4, ask_arg(mem, term, 4));
                link(mem, cal_6 + 5, ask_arg(mem, term, 9));
                link(mem, cal_6 + 6, ask_arg(mem, term, 6));
                link(mem, cal_6 + 7, Cal(3, 106, cal_5));
                u64 cal_7 = alloc(mem, 3);
                link(mem, cal_7 + 0, ask_arg(mem, term, 8));
                link(mem, cal_7 + 1, Cal(8, 7, cal_6));
                link(mem, cal_7 + 2, ask_arg(mem, term, 10));
                u64 done = Cal(3, 45, cal_7);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 12);
                clear(mem, get_loc(ask_arg(mem, term, 11), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 7));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 11), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 11), 1));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 11)) == CTR && get_ext(ask_arg(mem, term, 11)) == 139u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 12);
                clear(mem, get_loc(ask_arg(mem, term, 11), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 7));
                collect(mem, ask_arg(mem, term, 8));
                collect(mem, ask_arg(mem, term, 9));
                collect(mem, ask_arg(mem, term, 10));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 11), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 11), 1));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 11), 2));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 11)) == CTR && get_ext(ask_arg(mem, term, 11)) == 141u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_4));
                link(mem, cal_5 + 2, ask_arg(mem, ask_arg(mem, term, 11), 2));
                u64 cal_6 = alloc(mem, 8);
                link(mem, cal_6 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_6 + 1, ask_arg(mem, term, 1));
                link(mem, cal_6 + 2, Ctr(0, 5, ctr_1));
                link(mem, cal_6 + 3, Ctr(0, 5, ctr_2));
                link(mem, cal_6 + 4, ask_arg(mem, term, 4));
                link(mem, cal_6 + 5, ask_arg(mem, term, 10));
                link(mem, cal_6 + 6, Cal(3, 106, cal_5));
                link(mem, cal_6 + 7, ask_arg(mem, term, 7));
                u64 cal_7 = alloc(mem, 3);
                link(mem, cal_7 + 0, ask_arg(mem, term, 8));
                link(mem, cal_7 + 1, ask_arg(mem, term, 9));
                link(mem, cal_7 + 2, Cal(8, 7, cal_6));
                u64 done = Cal(3, 45, cal_7);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 12);
                clear(mem, get_loc(ask_arg(mem, term, 11), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 11), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 11), 1));
                init = 1;
                continue;
              }
              break;
            };
            case _JUST__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 179, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 lam_5 = alloc(mem, 2);
                u64 cal_6 = alloc(mem, 6);
                link(mem, cal_6 + 0, Var(lam_0));
                link(mem, cal_6 + 1, Var(lam_1));
                link(mem, cal_6 + 2, Var(lam_2));
                link(mem, cal_6 + 3, Var(lam_3));
                link(mem, cal_6 + 4, Var(lam_4));
                link(mem, cal_6 + 5, Var(lam_5));
                link(mem, lam_5 + 1, Cal(6, 20, cal_6));
                link(mem, lam_4 + 1, Lam(lam_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LT__2_: {
              if (1) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 0)) == U32 && get_tag(ask_arg(mem, term, 1)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 0)) <  get_val(ask_arg(mem, term, 1)) ? 1 : 0);
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 0));
                  link(mem, op2_1 + 1, ask_arg(mem, term, 1));
                  ret_0 = Op2(LTN, op2_1);
                }
                u64 cal_2 = alloc(mem, 1);
                link(mem, cal_2 + 0, ret_0);
                u64 done = Cal(1, 239, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 106, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FROMLIST__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 117, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__K__9_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 4));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 6));
                u64 done = Ctr(3, 18, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 9);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 7));
                collect(mem, ask_arg(mem, term, 8));
                init = 1;
                continue;
              }
              break;
            };
            case _EQUAL__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 9, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _FLATTEN__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 5);
                link(mem, cal_4 + 0, ask_arg(mem, term, 0));
                link(mem, cal_4 + 1, Var(lam_0));
                link(mem, cal_4 + 2, Var(lam_1));
                link(mem, cal_4 + 3, Var(lam_2));
                link(mem, cal_4 + 4, Var(lam_3));
                link(mem, lam_3 + 1, Cal(5, 121, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ORD_CONSTRUCTOR__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 71, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2264____0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__5_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 8);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, ask_arg(mem, term, 1));
                link(mem, cal_3 + 2, ask_arg(mem, term, 2));
                link(mem, cal_3 + 3, ask_arg(mem, term, 3));
                link(mem, cal_3 + 4, ask_arg(mem, term, 4));
                link(mem, cal_3 + 5, Var(lam_0));
                link(mem, cal_3 + 6, Var(lam_1));
                link(mem, cal_3 + 7, Var(lam_2));
                link(mem, lam_2 + 1, Cal(8, 7, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _ORD_CONSTRUCTOR__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 4);
                link(mem, cal_4 + 0, Var(lam_0));
                link(mem, cal_4 + 1, Var(lam_1));
                link(mem, cal_4 + 2, Var(lam_2));
                link(mem, cal_4 + 3, Var(lam_3));
                link(mem, lam_3 + 1, Cal(4, 71, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _SORT__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 80, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5D__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 22, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 lam_5 = alloc(mem, 2);
                u64 lam_6 = alloc(mem, 2);
                u64 lam_7 = alloc(mem, 2);
                u64 cal_8 = alloc(mem, 8);
                link(mem, cal_8 + 0, Var(lam_0));
                link(mem, cal_8 + 1, Var(lam_1));
                link(mem, cal_8 + 2, Var(lam_2));
                link(mem, cal_8 + 3, Var(lam_3));
                link(mem, cal_8 + 4, Var(lam_4));
                link(mem, cal_8 + 5, Var(lam_5));
                link(mem, cal_8 + 6, Var(lam_6));
                link(mem, cal_8 + 7, Var(lam_7));
                link(mem, lam_7 + 1, Cal(8, 7, cal_8));
                link(mem, lam_6 + 1, Lam(lam_7));
                link(mem, lam_5 + 1, Lam(lam_6));
                link(mem, lam_4 + 1, Lam(lam_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPMAYBE__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 4);
                link(mem, cal_4 + 0, Var(lam_0));
                link(mem, cal_4 + 1, Var(lam_1));
                link(mem, cal_4 + 2, Var(lam_2));
                link(mem, cal_4 + 3, Var(lam_3));
                link(mem, lam_3 + 1, Cal(4, 65, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DSUC__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 41, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _HERE__4_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 4);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                link(mem, ctr_0 + 3, ask_arg(mem, term, 3));
                u64 done = Ctr(4, 260, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _X5B__X5D__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 24, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DANTISYM__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINL__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 cal_5 = alloc(mem, 5);
                link(mem, cal_5 + 0, Var(lam_0));
                link(mem, cal_5 + 1, Var(lam_1));
                link(mem, cal_5 + 2, Var(lam_2));
                link(mem, cal_5 + 3, Var(lam_3));
                link(mem, cal_5 + 4, Var(lam_4));
                link(mem, lam_4 + 1, Cal(5, 16, cal_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _IT__2_: {
              if (1) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              break;
            };
            case _XAC____0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DX5BX5DX221E__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 69, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPMAYBE__SPLIT__D__4_: {
              if (get_tag(ask_arg(mem,term,3)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 3), 3);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 3)) == CTR && get_ext(ask_arg(mem, term, 3)) == 179u)) {
                inc_cost(mem);
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, ask_arg(mem, term, 2));
                link(mem, app_0 + 1, ask_arg(mem, ask_arg(mem, term, 3), 0));
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, App(app_0));
                u64 done = Cal(1, 140, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                clear(mem, get_loc(ask_arg(mem, term, 3), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 3)) == CTR && get_ext(ask_arg(mem, term, 3)) == 180u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 180, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                clear(mem, get_loc(ask_arg(mem, term, 3), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              break;
            };
            case _SUBST__4_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 6);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 2));
                link(mem, cal_2 + 3, ask_arg(mem, term, 3));
                link(mem, cal_2 + 4, Var(lam_0));
                link(mem, cal_2 + 5, Var(lam_1));
                link(mem, lam_1 + 1, Cal(6, 3, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                u64 done = Ctr(3, 107, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _TDOX2DNAT__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Cal(0, 70, cal_0));
                link(mem, cal_2 + 1, Cal(0, 148, cal_1));
                u64 done = Cal(2, 165, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TESTFROMLIST__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 0);
                u64 cal_3 = alloc(mem, 2);
                link(mem, cal_3 + 0, U_32(3));
                link(mem, cal_3 + 1, Cal(0, 21, cal_2));
                u64 cal_4 = alloc(mem, 2);
                link(mem, cal_4 + 0, U_32(2));
                link(mem, cal_4 + 1, Cal(2, 118, cal_3));
                u64 cal_5 = alloc(mem, 2);
                link(mem, cal_5 + 0, U_32(1));
                link(mem, cal_5 + 1, Cal(2, 118, cal_4));
                u64 cal_6 = alloc(mem, 3);
                link(mem, cal_6 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_6 + 1, Cal(0, 112, cal_1));
                link(mem, cal_6 + 2, Cal(2, 118, cal_5));
                u64 done = Cal(3, 117, cal_6);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__7_: {
              if (1) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, term, 6);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = ask_arg(mem, term, 5);
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 cpy_10 = ask_arg(mem, term, 4);
                u64 dp0_11;
                u64 dp1_12;
                if (get_tag(cpy_10) == U32) {
                  inc_cost(mem);
                  dp0_11 = cpy_10;
                  dp1_12 = cpy_10;
                } else {
                  u64 dup_13 = alloc(mem, 3);
                  u64 col_14 = gen_dupk(mem);
                  link(mem, dup_13 + 2, cpy_10);
                  dp0_11 = Dp0(col_14, dup_13);
                  dp1_12 = Dp1(col_14, dup_13);
                }
                u64 cpy_15 = ask_arg(mem, term, 3);
                u64 dp0_16;
                u64 dp1_17;
                if (get_tag(cpy_15) == U32) {
                  inc_cost(mem);
                  dp0_16 = cpy_15;
                  dp1_17 = cpy_15;
                } else {
                  u64 dup_18 = alloc(mem, 3);
                  u64 col_19 = gen_dupk(mem);
                  link(mem, dup_18 + 2, cpy_15);
                  dp0_16 = Dp0(col_19, dup_18);
                  dp1_17 = Dp1(col_19, dup_18);
                }
                u64 cpy_20 = ask_arg(mem, term, 2);
                u64 dp0_21;
                u64 dp1_22;
                if (get_tag(cpy_20) == U32) {
                  inc_cost(mem);
                  dp0_21 = cpy_20;
                  dp1_22 = cpy_20;
                } else {
                  u64 dup_23 = alloc(mem, 3);
                  u64 col_24 = gen_dupk(mem);
                  link(mem, dup_23 + 2, cpy_20);
                  dp0_21 = Dp0(col_24, dup_23);
                  dp1_22 = Dp1(col_24, dup_23);
                }
                u64 cpy_25 = ask_arg(mem, term, 1);
                u64 dp0_26;
                u64 dp1_27;
                if (get_tag(cpy_25) == U32) {
                  inc_cost(mem);
                  dp0_26 = cpy_25;
                  dp1_27 = cpy_25;
                } else {
                  u64 dup_28 = alloc(mem, 3);
                  u64 col_29 = gen_dupk(mem);
                  link(mem, dup_28 + 2, cpy_25);
                  dp0_26 = Dp0(col_29, dup_28);
                  dp1_27 = Dp1(col_29, dup_28);
                }
                u64 cpy_30 = ask_arg(mem, term, 0);
                u64 dp0_31;
                u64 dp1_32;
                if (get_tag(cpy_30) == U32) {
                  inc_cost(mem);
                  dp0_31 = cpy_30;
                  dp1_32 = cpy_30;
                } else {
                  u64 dup_33 = alloc(mem, 3);
                  u64 col_34 = gen_dupk(mem);
                  link(mem, dup_33 + 2, cpy_30);
                  dp0_31 = Dp0(col_34, dup_33);
                  dp1_32 = Dp1(col_34, dup_33);
                }
                u64 cal_35 = alloc(mem, 7);
                link(mem, cal_35 + 0, dp0_31);
                link(mem, cal_35 + 1, dp0_26);
                link(mem, cal_35 + 2, dp0_21);
                link(mem, cal_35 + 3, dp0_16);
                link(mem, cal_35 + 4, dp0_11);
                link(mem, cal_35 + 5, dp0_6);
                link(mem, cal_35 + 6, dp0_1);
                u64 cal_36 = alloc(mem, 8);
                link(mem, cal_36 + 0, dp1_32);
                link(mem, cal_36 + 1, dp1_27);
                link(mem, cal_36 + 2, dp1_22);
                link(mem, cal_36 + 3, dp1_17);
                link(mem, cal_36 + 4, dp1_12);
                link(mem, cal_36 + 5, dp1_7);
                link(mem, cal_36 + 6, dp1_2);
                link(mem, cal_36 + 7, Cal(7, 210, cal_35));
                u64 done = Cal(8, 211, cal_36);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 7);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DREFL__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 39, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 cal_3 = alloc(mem, 1);
                link(mem, cal_3 + 0, Cal(1, 40, cal_0));
                u64 cal_4 = alloc(mem, 3);
                link(mem, cal_4 + 0, Ctr(0, 5, ctr_1));
                link(mem, cal_4 + 1, Ctr(0, 5, ctr_2));
                link(mem, cal_4 + 2, Cal(1, 42, cal_3));
                u64 done = Cal(3, 41, cal_4);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 43u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, ask_arg(mem, term, 0), 1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 4);
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 2));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 3));
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 5);
                link(mem, cal_4 + 0, ask_arg(mem, term, 0));
                link(mem, cal_4 + 1, Var(lam_0));
                link(mem, cal_4 + 2, Var(lam_1));
                link(mem, cal_4 + 3, Var(lam_2));
                link(mem, cal_4 + 4, Var(lam_3));
                link(mem, lam_3 + 1, Cal(5, 96, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 103, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _EQUAL__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 9, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DSUC__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 41, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 6);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, ask_arg(mem, term, 1));
                link(mem, cal_3 + 2, ask_arg(mem, term, 2));
                link(mem, cal_3 + 3, Var(lam_0));
                link(mem, cal_3 + 4, Var(lam_1));
                link(mem, cal_3 + 5, Var(lam_2));
                link(mem, lam_2 + 1, Cal(6, 20, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2237____0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 118, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__H__7_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 249, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 7);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                init = 1;
                continue;
              }
              break;
            };
            case _FALSE__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 33, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _SORT__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_4));
                link(mem, cal_5 + 1, ask_arg(mem, term, 1));
                link(mem, cal_5 + 2, ask_arg(mem, term, 2));
                u64 cal_6 = alloc(mem, 5);
                link(mem, cal_6 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_6 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_6 + 2, Ctr(0, 5, ctr_2));
                link(mem, cal_6 + 3, Ctr(0, 5, ctr_3));
                link(mem, cal_6 + 4, Cal(3, 117, cal_5));
                u64 done = Cal(5, 121, cal_6);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 lam_5 = alloc(mem, 2);
                u64 lam_6 = alloc(mem, 2);
                u64 cal_7 = alloc(mem, 7);
                link(mem, cal_7 + 0, Var(lam_0));
                link(mem, cal_7 + 1, Var(lam_1));
                link(mem, cal_7 + 2, Var(lam_2));
                link(mem, cal_7 + 3, Var(lam_3));
                link(mem, cal_7 + 4, Var(lam_4));
                link(mem, cal_7 + 5, Var(lam_5));
                link(mem, cal_7 + 6, Var(lam_6));
                link(mem, lam_6 + 1, Cal(7, 47, cal_7));
                link(mem, lam_5 + 1, Lam(lam_6));
                link(mem, lam_4 + 1, Lam(lam_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 43u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, ask_arg(mem, term, 0), 2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 4);
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 1));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 3));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DREFL__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 11, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__SPLIT__B__3_: {
              if (get_tag(ask_arg(mem,term,1)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 1), 1);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == U32 && get_val(ask_arg(mem, term, 1)) == 0u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 3);
                link(mem, cal_4 + 0, U_32(0));
                link(mem, cal_4 + 1, Ctr(0, 5, ctr_2));
                link(mem, cal_4 + 2, Ctr(0, 5, ctr_3));
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_5 + 2, Cal(3, 58, cal_4));
                u64 done = Cal(3, 105, cal_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, term, 2);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = dp0_1;
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 cpy_10 = ask_arg(mem, term, 1);
                u64 dp0_11;
                u64 dp1_12;
                if (get_tag(cpy_10) == U32) {
                  inc_cost(mem);
                  dp0_11 = cpy_10;
                  dp1_12 = cpy_10;
                } else {
                  u64 dup_13 = alloc(mem, 3);
                  u64 col_14 = gen_dupk(mem);
                  link(mem, dup_13 + 2, cpy_10);
                  dp0_11 = Dp0(col_14, dup_13);
                  dp1_12 = Dp1(col_14, dup_13);
                }
                u64 cpy_15 = dp0_11;
                u64 dp0_16;
                u64 dp1_17;
                if (get_tag(cpy_15) == U32) {
                  inc_cost(mem);
                  dp0_16 = cpy_15;
                  dp1_17 = cpy_15;
                } else {
                  u64 dup_18 = alloc(mem, 3);
                  u64 col_19 = gen_dupk(mem);
                  link(mem, dup_18 + 2, cpy_15);
                  dp0_16 = Dp0(col_19, dup_18);
                  dp1_17 = Dp1(col_19, dup_18);
                }
                u64 cpy_20 = ask_arg(mem, term, 0);
                u64 dp0_21;
                u64 dp1_22;
                if (get_tag(cpy_20) == U32) {
                  inc_cost(mem);
                  dp0_21 = cpy_20;
                  dp1_22 = cpy_20;
                } else {
                  u64 dup_23 = alloc(mem, 3);
                  u64 col_24 = gen_dupk(mem);
                  link(mem, dup_23 + 2, cpy_20);
                  dp0_21 = Dp0(col_24, dup_23);
                  dp1_22 = Dp1(col_24, dup_23);
                }
                u64 cpy_25 = dp0_21;
                u64 dp0_26;
                u64 dp1_27;
                if (get_tag(cpy_25) == U32) {
                  inc_cost(mem);
                  dp0_26 = cpy_25;
                  dp1_27 = cpy_25;
                } else {
                  u64 dup_28 = alloc(mem, 3);
                  u64 col_29 = gen_dupk(mem);
                  link(mem, dup_28 + 2, cpy_25);
                  dp0_26 = Dp0(col_29, dup_28);
                  dp1_27 = Dp1(col_29, dup_28);
                }
                u64 cal_33 = alloc(mem, 3);
                link(mem, cal_33 + 0, dp1_22);
                link(mem, cal_33 + 1, dp1_12);
                link(mem, cal_33 + 2, dp1_2);
                u64 cpy_30 = Cal(3, 199, cal_33);
                u64 dp0_31;
                u64 dp1_32;
                if (get_tag(cpy_30) == U32) {
                  inc_cost(mem);
                  dp0_31 = cpy_30;
                  dp1_32 = cpy_30;
                } else {
                  u64 dup_34 = alloc(mem, 3);
                  u64 col_35 = gen_dupk(mem);
                  link(mem, dup_34 + 2, cpy_30);
                  dp0_31 = Dp0(col_35, dup_34);
                  dp1_32 = Dp1(col_35, dup_34);
                }
                u64 cal_36 = alloc(mem, 4);
                link(mem, cal_36 + 0, dp0_26);
                link(mem, cal_36 + 1, dp0_16);
                link(mem, cal_36 + 2, dp0_6);
                link(mem, cal_36 + 3, dp0_31);
                u64 cal_37 = alloc(mem, 5);
                link(mem, cal_37 + 0, dp1_27);
                link(mem, cal_37 + 1, dp1_17);
                link(mem, cal_37 + 2, dp1_7);
                link(mem, cal_37 + 3, dp1_32);
                link(mem, cal_37 + 4, Cal(4, 200, cal_36));
                u64 done = Cal(5, 201, cal_37);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _TRUE__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 32, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINL__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 5);
                link(mem, cal_4 + 0, ask_arg(mem, term, 0));
                link(mem, cal_4 + 1, Var(lam_0));
                link(mem, cal_4 + 2, Var(lam_1));
                link(mem, cal_4 + 3, Var(lam_2));
                link(mem, cal_4 + 4, Var(lam_3));
                link(mem, lam_3 + 1, Cal(5, 16, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DX5BX5DX221E__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 69, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINR__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 5);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, ask_arg(mem, term, 1));
                link(mem, cal_3 + 2, Var(lam_0));
                link(mem, cal_3 + 3, Var(lam_1));
                link(mem, cal_3 + 4, Var(lam_2));
                link(mem, lam_2 + 1, Cal(5, 94, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _LEAF__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 49, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINL__4_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 5);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, ask_arg(mem, term, 3));
                link(mem, cal_1 + 4, Var(lam_0));
                link(mem, lam_0 + 1, Cal(5, 16, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _INR__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 91, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__SPLIT__D__5_: {
              if (get_tag(ask_arg(mem,term,3)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 3), 3);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 3)) == CTR && get_ext(ask_arg(mem, term, 3)) == 54u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 39, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 3), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 3), 0));
                collect(mem, ask_arg(mem, term, 4));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 3)) == CTR && get_ext(ask_arg(mem, term, 3)) == 156u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 3), 2);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = ask_arg(mem, ask_arg(mem, term, 3), 1);
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 3), 0);
                u64 dp0_11;
                u64 dp1_12;
                if (get_tag(cpy_10) == U32) {
                  inc_cost(mem);
                  dp0_11 = cpy_10;
                  dp1_12 = cpy_10;
                } else {
                  u64 dup_13 = alloc(mem, 3);
                  u64 col_14 = gen_dupk(mem);
                  link(mem, dup_13 + 2, cpy_10);
                  dp0_11 = Dp0(col_14, dup_13);
                  dp1_12 = Dp1(col_14, dup_13);
                }
                u64 ctr_15 = alloc(mem, 3);
                link(mem, ctr_15 + 0, dp0_11);
                link(mem, ctr_15 + 1, dp0_6);
                link(mem, ctr_15 + 2, dp0_1);
                u64 cal_16 = alloc(mem, 8);
                link(mem, cal_16 + 0, ask_arg(mem, term, 0));
                link(mem, cal_16 + 1, ask_arg(mem, term, 1));
                link(mem, cal_16 + 2, ask_arg(mem, term, 2));
                link(mem, cal_16 + 3, Ctr(3, 156, ctr_15));
                link(mem, cal_16 + 4, ask_arg(mem, term, 4));
                link(mem, cal_16 + 5, dp1_12);
                link(mem, cal_16 + 6, dp1_7);
                link(mem, cal_16 + 7, dp1_2);
                u64 done = Cal(8, 155, cal_16);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 3), 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264X2DI__4_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_2 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 3));
                u64 done = Cal(3, 106, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__F__8_: {
              if (get_tag(ask_arg(mem,term,5)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 5), 5);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 5)) == CTR && get_ext(ask_arg(mem, term, 5)) == 222u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 114, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 8);
                clear(mem, get_loc(ask_arg(mem, term, 5), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 5), 0));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 7));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 5)) == CTR && get_ext(ask_arg(mem, term, 5)) == 107u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 5), 2);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = ask_arg(mem, ask_arg(mem, term, 5), 1);
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 5), 0);
                u64 dp0_11;
                u64 dp1_12;
                if (get_tag(cpy_10) == U32) {
                  inc_cost(mem);
                  dp0_11 = cpy_10;
                  dp1_12 = cpy_10;
                } else {
                  u64 dup_13 = alloc(mem, 3);
                  u64 col_14 = gen_dupk(mem);
                  link(mem, dup_13 + 2, cpy_10);
                  dp0_11 = Dp0(col_14, dup_13);
                  dp1_12 = Dp1(col_14, dup_13);
                }
                u64 ctr_15 = alloc(mem, 3);
                link(mem, ctr_15 + 0, dp0_11);
                link(mem, ctr_15 + 1, dp0_6);
                link(mem, ctr_15 + 2, dp0_1);
                u64 cal_16 = alloc(mem, 11);
                link(mem, cal_16 + 0, ask_arg(mem, term, 0));
                link(mem, cal_16 + 1, ask_arg(mem, term, 1));
                link(mem, cal_16 + 2, ask_arg(mem, term, 2));
                link(mem, cal_16 + 3, ask_arg(mem, term, 3));
                link(mem, cal_16 + 4, ask_arg(mem, term, 4));
                link(mem, cal_16 + 5, Ctr(3, 107, ctr_15));
                link(mem, cal_16 + 6, ask_arg(mem, term, 6));
                link(mem, cal_16 + 7, ask_arg(mem, term, 7));
                link(mem, cal_16 + 8, dp1_12);
                link(mem, cal_16 + 9, dp1_7);
                link(mem, cal_16 + 10, dp1_2);
                u64 done = Cal(11, 223, cal_16);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 8);
                clear(mem, get_loc(ask_arg(mem, term, 5), 0), 3);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 7);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 8);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__4_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 7);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, ask_arg(mem, term, 1));
                link(mem, cal_3 + 2, ask_arg(mem, term, 2));
                link(mem, cal_3 + 3, ask_arg(mem, term, 3));
                link(mem, cal_3 + 4, Var(lam_0));
                link(mem, cal_3 + 5, Var(lam_1));
                link(mem, cal_3 + 6, Var(lam_2));
                link(mem, lam_2 + 1, Cal(7, 47, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _TEST1__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 0);
                u64 cal_3 = alloc(mem, 2);
                link(mem, cal_3 + 0, U_32(4));
                link(mem, cal_3 + 1, Cal(0, 21, cal_2));
                u64 cal_4 = alloc(mem, 2);
                link(mem, cal_4 + 0, U_32(5));
                link(mem, cal_4 + 1, Cal(2, 118, cal_3));
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_5 + 1, Cal(0, 112, cal_1));
                link(mem, cal_5 + 2, Cal(2, 118, cal_4));
                u64 done = Cal(3, 80, cal_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2BX221EX2DX2264X2DI__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 14, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__E__4_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 2);
                link(mem, cal_0 + 0, ask_arg(mem, term, 2));
                link(mem, cal_0 + 1, ask_arg(mem, term, 3));
                u64 done = Cal(2, 52, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _NOTHING__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 180, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__C__11_: {
              if (get_tag(ask_arg(mem,term,2)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 2), 2);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 24u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 2), 0);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 ctr_5 = alloc(mem, 1);
                link(mem, ctr_5 + 0, dp0_1);
                u64 cal_6 = alloc(mem, 12);
                link(mem, cal_6 + 0, ask_arg(mem, term, 0));
                link(mem, cal_6 + 1, ask_arg(mem, term, 1));
                link(mem, cal_6 + 2, Ctr(1, 24, ctr_5));
                link(mem, cal_6 + 3, ask_arg(mem, term, 3));
                link(mem, cal_6 + 4, ask_arg(mem, term, 4));
                link(mem, cal_6 + 5, ask_arg(mem, term, 5));
                link(mem, cal_6 + 6, ask_arg(mem, term, 6));
                link(mem, cal_6 + 7, ask_arg(mem, term, 7));
                link(mem, cal_6 + 8, ask_arg(mem, term, 8));
                link(mem, cal_6 + 9, ask_arg(mem, term, 9));
                link(mem, cal_6 + 10, ask_arg(mem, term, 10));
                link(mem, cal_6 + 11, dp1_2);
                u64 done = Cal(12, 23, cal_6);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 11);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 1);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 7);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 11);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 8));
                collect(mem, ask_arg(mem, term, 9));
                collect(mem, ask_arg(mem, term, 10));
                init = 1;
                continue;
              }
              break;
            };
            case _SUBST__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 cal_5 = alloc(mem, 6);
                link(mem, cal_5 + 0, ask_arg(mem, term, 0));
                link(mem, cal_5 + 1, Var(lam_0));
                link(mem, cal_5 + 2, Var(lam_1));
                link(mem, cal_5 + 3, Var(lam_2));
                link(mem, cal_5 + 4, Var(lam_3));
                link(mem, cal_5 + 5, Var(lam_4));
                link(mem, lam_4 + 1, Cal(6, 3, cal_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DDEC__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 58, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _SUBST__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 6);
                link(mem, cal_4 + 0, ask_arg(mem, term, 0));
                link(mem, cal_4 + 1, ask_arg(mem, term, 1));
                link(mem, cal_4 + 2, Var(lam_0));
                link(mem, cal_4 + 3, Var(lam_1));
                link(mem, cal_4 + 4, Var(lam_2));
                link(mem, cal_4 + 5, Var(lam_3));
                link(mem, lam_3 + 1, Cal(6, 3, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2265____0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2BX221E__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 62, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FLATTEN__SPLIT__E__5_: {
              if (get_tag(ask_arg(mem,term,4)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 4), 4);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 49u)) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 21, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 0));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 184u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 5);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_1));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_2));
                link(mem, cal_5 + 2, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 3, Ctr(0, 5, ctr_4));
                link(mem, cal_5 + 4, ask_arg(mem, ask_arg(mem, term, 4), 1));
                u64 ctr_6 = alloc(mem, 0);
                u64 ctr_7 = alloc(mem, 0);
                u64 ctr_8 = alloc(mem, 0);
                u64 ctr_9 = alloc(mem, 0);
                u64 cal_10 = alloc(mem, 5);
                link(mem, cal_10 + 0, Ctr(0, 5, ctr_6));
                link(mem, cal_10 + 1, Ctr(0, 5, ctr_7));
                link(mem, cal_10 + 2, Ctr(0, 5, ctr_8));
                link(mem, cal_10 + 3, Ctr(0, 5, ctr_9));
                link(mem, cal_10 + 4, ask_arg(mem, ask_arg(mem, term, 4), 2));
                u64 cal_11 = alloc(mem, 2);
                link(mem, cal_11 + 0, ask_arg(mem, ask_arg(mem, term, 4), 0));
                link(mem, cal_11 + 1, Cal(5, 121, cal_10));
                u64 cal_12 = alloc(mem, 3);
                link(mem, cal_12 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_12 + 1, Cal(5, 121, cal_5));
                link(mem, cal_12 + 2, Cal(2, 118, cal_11));
                u64 done = Cal(3, 161, cal_12);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 5);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, ask_arg(mem, term, 1));
                link(mem, cal_3 + 2, Var(lam_0));
                link(mem, cal_3 + 3, Var(lam_1));
                link(mem, cal_3 + 4, Var(lam_2));
                link(mem, lam_2 + 1, Cal(5, 96, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__4_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 6);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 2));
                link(mem, cal_2 + 3, ask_arg(mem, term, 3));
                link(mem, cal_2 + 4, Var(lam_0));
                link(mem, cal_2 + 5, Var(lam_1));
                link(mem, lam_1 + 1, Cal(6, 20, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2BX2B____SPLIT__B__3_: {
              if (get_tag(ask_arg(mem,term,1)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 1), 1);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 22u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 1), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 218u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_1 + 1, ask_arg(mem, ask_arg(mem, term, 1), 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, ask_arg(mem, ask_arg(mem, term, 1), 0));
                link(mem, cal_2 + 1, Cal(3, 161, cal_1));
                u64 done = Cal(2, 118, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 1), 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              break;
            };
            case _FST__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 56, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPMAYBE__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 65, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__7_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 8);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, ask_arg(mem, term, 3));
                link(mem, cal_1 + 4, ask_arg(mem, term, 4));
                link(mem, cal_1 + 5, ask_arg(mem, term, 5));
                link(mem, cal_1 + 6, ask_arg(mem, term, 6));
                link(mem, cal_1 + 7, Var(lam_0));
                link(mem, lam_0 + 1, Cal(8, 7, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 7);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__SPLIT__B__2_: {
              if (get_tag(ask_arg(mem,term,1)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 1), 1);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == U32 && get_val(ask_arg(mem, term, 1)) == 0u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_3 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_3 + 2, Ctr(0, 5, ctr_2));
                u64 done = Cal(3, 9, cal_3);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 3);
                link(mem, cal_4 + 0, U_32(0));
                link(mem, cal_4 + 1, Ctr(0, 5, ctr_2));
                link(mem, cal_4 + 2, Ctr(0, 5, ctr_3));
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_5 + 2, Cal(3, 58, cal_4));
                u64 done = Cal(3, 67, cal_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__SPLIT__F__6_: {
              if (get_tag(ask_arg(mem,term,5)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 5), 5);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 5)) == CTR && get_ext(ask_arg(mem, term, 5)) == 49u)) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 259, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 6);
                clear(mem, get_loc(ask_arg(mem, term, 5), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 5), 0));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 5)) == CTR && get_ext(ask_arg(mem, term, 5)) == 184u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 5), 2);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = dp0_1;
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 5), 1);
                u64 dp0_11;
                u64 dp1_12;
                if (get_tag(cpy_10) == U32) {
                  inc_cost(mem);
                  dp0_11 = cpy_10;
                  dp1_12 = cpy_10;
                } else {
                  u64 dup_13 = alloc(mem, 3);
                  u64 col_14 = gen_dupk(mem);
                  link(mem, dup_13 + 2, cpy_10);
                  dp0_11 = Dp0(col_14, dup_13);
                  dp1_12 = Dp1(col_14, dup_13);
                }
                u64 cpy_15 = dp0_11;
                u64 dp0_16;
                u64 dp1_17;
                if (get_tag(cpy_15) == U32) {
                  inc_cost(mem);
                  dp0_16 = cpy_15;
                  dp1_17 = cpy_15;
                } else {
                  u64 dup_18 = alloc(mem, 3);
                  u64 col_19 = gen_dupk(mem);
                  link(mem, dup_18 + 2, cpy_15);
                  dp0_16 = Dp0(col_19, dup_18);
                  dp1_17 = Dp1(col_19, dup_18);
                }
                u64 cpy_20 = ask_arg(mem, ask_arg(mem, term, 5), 0);
                u64 dp0_21;
                u64 dp1_22;
                if (get_tag(cpy_20) == U32) {
                  inc_cost(mem);
                  dp0_21 = cpy_20;
                  dp1_22 = cpy_20;
                } else {
                  u64 dup_23 = alloc(mem, 3);
                  u64 col_24 = gen_dupk(mem);
                  link(mem, dup_23 + 2, cpy_20);
                  dp0_21 = Dp0(col_24, dup_23);
                  dp1_22 = Dp1(col_24, dup_23);
                }
                u64 cpy_25 = dp0_21;
                u64 dp0_26;
                u64 dp1_27;
                if (get_tag(cpy_25) == U32) {
                  inc_cost(mem);
                  dp0_26 = cpy_25;
                  dp1_27 = cpy_25;
                } else {
                  u64 dup_28 = alloc(mem, 3);
                  u64 col_29 = gen_dupk(mem);
                  link(mem, dup_28 + 2, cpy_25);
                  dp0_26 = Dp0(col_29, dup_28);
                  dp1_27 = Dp1(col_29, dup_28);
                }
                u64 cpy_30 = ask_arg(mem, term, 4);
                u64 dp0_31;
                u64 dp1_32;
                if (get_tag(cpy_30) == U32) {
                  inc_cost(mem);
                  dp0_31 = cpy_30;
                  dp1_32 = cpy_30;
                } else {
                  u64 dup_33 = alloc(mem, 3);
                  u64 col_34 = gen_dupk(mem);
                  link(mem, dup_33 + 2, cpy_30);
                  dp0_31 = Dp0(col_34, dup_33);
                  dp1_32 = Dp1(col_34, dup_33);
                }
                u64 cpy_35 = ask_arg(mem, term, 3);
                u64 dp0_36;
                u64 dp1_37;
                if (get_tag(cpy_35) == U32) {
                  inc_cost(mem);
                  dp0_36 = cpy_35;
                  dp1_37 = cpy_35;
                } else {
                  u64 dup_38 = alloc(mem, 3);
                  u64 col_39 = gen_dupk(mem);
                  link(mem, dup_38 + 2, cpy_35);
                  dp0_36 = Dp0(col_39, dup_38);
                  dp1_37 = Dp1(col_39, dup_38);
                }
                u64 cpy_40 = ask_arg(mem, term, 2);
                u64 dp0_41;
                u64 dp1_42;
                if (get_tag(cpy_40) == U32) {
                  inc_cost(mem);
                  dp0_41 = cpy_40;
                  dp1_42 = cpy_40;
                } else {
                  u64 dup_43 = alloc(mem, 3);
                  u64 col_44 = gen_dupk(mem);
                  link(mem, dup_43 + 2, cpy_40);
                  dp0_41 = Dp0(col_44, dup_43);
                  dp1_42 = Dp1(col_44, dup_43);
                }
                u64 cpy_45 = ask_arg(mem, term, 1);
                u64 dp0_46;
                u64 dp1_47;
                if (get_tag(cpy_45) == U32) {
                  inc_cost(mem);
                  dp0_46 = cpy_45;
                  dp1_47 = cpy_45;
                } else {
                  u64 dup_48 = alloc(mem, 3);
                  u64 col_49 = gen_dupk(mem);
                  link(mem, dup_48 + 2, cpy_45);
                  dp0_46 = Dp0(col_49, dup_48);
                  dp1_47 = Dp1(col_49, dup_48);
                }
                u64 cpy_50 = ask_arg(mem, term, 0);
                u64 dp0_51;
                u64 dp1_52;
                if (get_tag(cpy_50) == U32) {
                  inc_cost(mem);
                  dp0_51 = cpy_50;
                  dp1_52 = cpy_50;
                } else {
                  u64 dup_53 = alloc(mem, 3);
                  u64 col_54 = gen_dupk(mem);
                  link(mem, dup_53 + 2, cpy_50);
                  dp0_51 = Dp0(col_54, dup_53);
                  dp1_52 = Dp1(col_54, dup_53);
                }
                u64 ctr_58 = alloc(mem, 3);
                link(mem, ctr_58 + 0, dp1_22);
                link(mem, ctr_58 + 1, dp1_12);
                link(mem, ctr_58 + 2, dp1_2);
                u64 cpy_55 = Ctr(3, 184, ctr_58);
                u64 dp0_56;
                u64 dp1_57;
                if (get_tag(cpy_55) == U32) {
                  inc_cost(mem);
                  dp0_56 = cpy_55;
                  dp1_57 = cpy_55;
                } else {
                  u64 dup_59 = alloc(mem, 3);
                  u64 col_60 = gen_dupk(mem);
                  link(mem, dup_59 + 2, cpy_55);
                  dp0_56 = Dp0(col_60, dup_59);
                  dp1_57 = Dp1(col_60, dup_59);
                }
                u64 cal_61 = alloc(mem, 9);
                link(mem, cal_61 + 0, dp0_51);
                link(mem, cal_61 + 1, dp0_46);
                link(mem, cal_61 + 2, dp0_41);
                link(mem, cal_61 + 3, dp0_36);
                link(mem, cal_61 + 4, dp0_31);
                link(mem, cal_61 + 5, dp0_56);
                link(mem, cal_61 + 6, dp0_26);
                link(mem, cal_61 + 7, dp0_16);
                link(mem, cal_61 + 8, dp0_6);
                u64 cal_62 = alloc(mem, 10);
                link(mem, cal_62 + 0, dp1_52);
                link(mem, cal_62 + 1, dp1_47);
                link(mem, cal_62 + 2, dp1_42);
                link(mem, cal_62 + 3, dp1_37);
                link(mem, cal_62 + 4, dp1_32);
                link(mem, cal_62 + 5, dp1_57);
                link(mem, cal_62 + 6, dp1_27);
                link(mem, cal_62 + 7, dp1_17);
                link(mem, cal_62 + 8, dp1_7);
                link(mem, cal_62 + 9, Cal(9, 17, cal_61));
                u64 done = Cal(10, 136, cal_62);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 6);
                clear(mem, get_loc(ask_arg(mem, term, 5), 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _MONUS__SPLIT__3_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 1u)) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 1)) == U32 && get_tag(ask_arg(mem, term, 2)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 1)) - get_val(ask_arg(mem, term, 2)));
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 1));
                  link(mem, op2_1 + 1, ask_arg(mem, term, 2));
                  ret_0 = Op2(SUB, op2_1);
                }
                u64 done = ret_0;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 done = U_32(0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              break;
            };
            case _X2DX221EX2DX2264__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 114, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LEFT__4_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 4);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                link(mem, ctr_0 + 3, ask_arg(mem, term, 3));
                u64 done = Ctr(4, 277, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__SPLIT__F__8_: {
              if (get_tag(ask_arg(mem,term,5)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 5), 5);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 5)) == CTR && get_ext(ask_arg(mem, term, 5)) == 49u)) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 6));
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, ask_arg(mem, term, 7));
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 4));
                link(mem, cal_2 + 1, Cal(1, 48, cal_0));
                link(mem, cal_2 + 2, Cal(1, 48, cal_1));
                u64 done = Cal(3, 45, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 8);
                clear(mem, get_loc(ask_arg(mem, term, 5), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 5), 0));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 5)) == CTR && get_ext(ask_arg(mem, term, 5)) == 184u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 5), 2);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = dp0_1;
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 5), 1);
                u64 dp0_11;
                u64 dp1_12;
                if (get_tag(cpy_10) == U32) {
                  inc_cost(mem);
                  dp0_11 = cpy_10;
                  dp1_12 = cpy_10;
                } else {
                  u64 dup_13 = alloc(mem, 3);
                  u64 col_14 = gen_dupk(mem);
                  link(mem, dup_13 + 2, cpy_10);
                  dp0_11 = Dp0(col_14, dup_13);
                  dp1_12 = Dp1(col_14, dup_13);
                }
                u64 cpy_15 = dp0_11;
                u64 dp0_16;
                u64 dp1_17;
                if (get_tag(cpy_15) == U32) {
                  inc_cost(mem);
                  dp0_16 = cpy_15;
                  dp1_17 = cpy_15;
                } else {
                  u64 dup_18 = alloc(mem, 3);
                  u64 col_19 = gen_dupk(mem);
                  link(mem, dup_18 + 2, cpy_15);
                  dp0_16 = Dp0(col_19, dup_18);
                  dp1_17 = Dp1(col_19, dup_18);
                }
                u64 cpy_20 = ask_arg(mem, ask_arg(mem, term, 5), 0);
                u64 dp0_21;
                u64 dp1_22;
                if (get_tag(cpy_20) == U32) {
                  inc_cost(mem);
                  dp0_21 = cpy_20;
                  dp1_22 = cpy_20;
                } else {
                  u64 dup_23 = alloc(mem, 3);
                  u64 col_24 = gen_dupk(mem);
                  link(mem, dup_23 + 2, cpy_20);
                  dp0_21 = Dp0(col_24, dup_23);
                  dp1_22 = Dp1(col_24, dup_23);
                }
                u64 cpy_25 = dp0_21;
                u64 dp0_26;
                u64 dp1_27;
                if (get_tag(cpy_25) == U32) {
                  inc_cost(mem);
                  dp0_26 = cpy_25;
                  dp1_27 = cpy_25;
                } else {
                  u64 dup_28 = alloc(mem, 3);
                  u64 col_29 = gen_dupk(mem);
                  link(mem, dup_28 + 2, cpy_25);
                  dp0_26 = Dp0(col_29, dup_28);
                  dp1_27 = Dp1(col_29, dup_28);
                }
                u64 cpy_30 = ask_arg(mem, term, 7);
                u64 dp0_31;
                u64 dp1_32;
                if (get_tag(cpy_30) == U32) {
                  inc_cost(mem);
                  dp0_31 = cpy_30;
                  dp1_32 = cpy_30;
                } else {
                  u64 dup_33 = alloc(mem, 3);
                  u64 col_34 = gen_dupk(mem);
                  link(mem, dup_33 + 2, cpy_30);
                  dp0_31 = Dp0(col_34, dup_33);
                  dp1_32 = Dp1(col_34, dup_33);
                }
                u64 cpy_35 = ask_arg(mem, term, 6);
                u64 dp0_36;
                u64 dp1_37;
                if (get_tag(cpy_35) == U32) {
                  inc_cost(mem);
                  dp0_36 = cpy_35;
                  dp1_37 = cpy_35;
                } else {
                  u64 dup_38 = alloc(mem, 3);
                  u64 col_39 = gen_dupk(mem);
                  link(mem, dup_38 + 2, cpy_35);
                  dp0_36 = Dp0(col_39, dup_38);
                  dp1_37 = Dp1(col_39, dup_38);
                }
                u64 cpy_40 = ask_arg(mem, term, 4);
                u64 dp0_41;
                u64 dp1_42;
                if (get_tag(cpy_40) == U32) {
                  inc_cost(mem);
                  dp0_41 = cpy_40;
                  dp1_42 = cpy_40;
                } else {
                  u64 dup_43 = alloc(mem, 3);
                  u64 col_44 = gen_dupk(mem);
                  link(mem, dup_43 + 2, cpy_40);
                  dp0_41 = Dp0(col_44, dup_43);
                  dp1_42 = Dp1(col_44, dup_43);
                }
                u64 cpy_45 = ask_arg(mem, term, 3);
                u64 dp0_46;
                u64 dp1_47;
                if (get_tag(cpy_45) == U32) {
                  inc_cost(mem);
                  dp0_46 = cpy_45;
                  dp1_47 = cpy_45;
                } else {
                  u64 dup_48 = alloc(mem, 3);
                  u64 col_49 = gen_dupk(mem);
                  link(mem, dup_48 + 2, cpy_45);
                  dp0_46 = Dp0(col_49, dup_48);
                  dp1_47 = Dp1(col_49, dup_48);
                }
                u64 cpy_50 = ask_arg(mem, term, 2);
                u64 dp0_51;
                u64 dp1_52;
                if (get_tag(cpy_50) == U32) {
                  inc_cost(mem);
                  dp0_51 = cpy_50;
                  dp1_52 = cpy_50;
                } else {
                  u64 dup_53 = alloc(mem, 3);
                  u64 col_54 = gen_dupk(mem);
                  link(mem, dup_53 + 2, cpy_50);
                  dp0_51 = Dp0(col_54, dup_53);
                  dp1_52 = Dp1(col_54, dup_53);
                }
                u64 cpy_55 = ask_arg(mem, term, 1);
                u64 dp0_56;
                u64 dp1_57;
                if (get_tag(cpy_55) == U32) {
                  inc_cost(mem);
                  dp0_56 = cpy_55;
                  dp1_57 = cpy_55;
                } else {
                  u64 dup_58 = alloc(mem, 3);
                  u64 col_59 = gen_dupk(mem);
                  link(mem, dup_58 + 2, cpy_55);
                  dp0_56 = Dp0(col_59, dup_58);
                  dp1_57 = Dp1(col_59, dup_58);
                }
                u64 cpy_60 = ask_arg(mem, term, 0);
                u64 dp0_61;
                u64 dp1_62;
                if (get_tag(cpy_60) == U32) {
                  inc_cost(mem);
                  dp0_61 = cpy_60;
                  dp1_62 = cpy_60;
                } else {
                  u64 dup_63 = alloc(mem, 3);
                  u64 col_64 = gen_dupk(mem);
                  link(mem, dup_63 + 2, cpy_60);
                  dp0_61 = Dp0(col_64, dup_63);
                  dp1_62 = Dp1(col_64, dup_63);
                }
                u64 ctr_68 = alloc(mem, 3);
                link(mem, ctr_68 + 0, dp1_22);
                link(mem, ctr_68 + 1, dp1_12);
                link(mem, ctr_68 + 2, dp1_2);
                u64 cpy_65 = Ctr(3, 184, ctr_68);
                u64 dp0_66;
                u64 dp1_67;
                if (get_tag(cpy_65) == U32) {
                  inc_cost(mem);
                  dp0_66 = cpy_65;
                  dp1_67 = cpy_65;
                } else {
                  u64 dup_69 = alloc(mem, 3);
                  u64 col_70 = gen_dupk(mem);
                  link(mem, dup_69 + 2, cpy_65);
                  dp0_66 = Dp0(col_70, dup_69);
                  dp1_67 = Dp1(col_70, dup_69);
                }
                u64 cal_71 = alloc(mem, 11);
                link(mem, cal_71 + 0, dp0_61);
                link(mem, cal_71 + 1, dp0_56);
                link(mem, cal_71 + 2, dp0_51);
                link(mem, cal_71 + 3, dp0_46);
                link(mem, cal_71 + 4, dp0_41);
                link(mem, cal_71 + 5, dp0_66);
                link(mem, cal_71 + 6, dp0_36);
                link(mem, cal_71 + 7, dp0_31);
                link(mem, cal_71 + 8, dp0_26);
                link(mem, cal_71 + 9, dp0_16);
                link(mem, cal_71 + 10, dp0_6);
                u64 cal_72 = alloc(mem, 12);
                link(mem, cal_72 + 0, dp1_62);
                link(mem, cal_72 + 1, dp1_57);
                link(mem, cal_72 + 2, dp1_52);
                link(mem, cal_72 + 3, dp1_47);
                link(mem, cal_72 + 4, dp1_42);
                link(mem, cal_72 + 5, dp1_67);
                link(mem, cal_72 + 6, dp1_37);
                link(mem, cal_72 + 7, dp1_32);
                link(mem, cal_72 + 8, dp1_27);
                link(mem, cal_72 + 9, dp1_17);
                link(mem, cal_72 + 10, dp1_7);
                link(mem, cal_72 + 11, Cal(11, 285, cal_71));
                u64 done = Cal(12, 185, cal_72);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 8);
                clear(mem, get_loc(ask_arg(mem, term, 5), 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _SORT__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 80, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _IT__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 12, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__E__16_: {
              if (get_tag(ask_arg(mem,term,4)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 4), 4);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 24u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 6);
                link(mem, ctr_2 + 0, ask_arg(mem, term, 1));
                link(mem, ctr_2 + 1, ask_arg(mem, term, 11));
                link(mem, ctr_2 + 2, ask_arg(mem, term, 12));
                link(mem, ctr_2 + 3, ask_arg(mem, ask_arg(mem, term, 4), 0));
                link(mem, ctr_2 + 4, ask_arg(mem, term, 10));
                link(mem, ctr_2 + 5, ask_arg(mem, term, 15));
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_3 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_3 + 2, Ctr(6, 291, ctr_2));
                u64 done = Cal(3, 106, cal_3);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 16);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 7));
                collect(mem, ask_arg(mem, term, 8));
                collect(mem, ask_arg(mem, term, 9));
                collect(mem, ask_arg(mem, term, 13));
                collect(mem, ask_arg(mem, term, 14));
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 7);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 16);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 8));
                collect(mem, ask_arg(mem, term, 9));
                collect(mem, ask_arg(mem, term, 10));
                collect(mem, ask_arg(mem, term, 11));
                collect(mem, ask_arg(mem, term, 12));
                collect(mem, ask_arg(mem, term, 13));
                collect(mem, ask_arg(mem, term, 14));
                collect(mem, ask_arg(mem, term, 15));
                init = 1;
                continue;
              }
              break;
            };
            case _TDO_CONSTRUCTOR__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 165, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _REFL__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 293, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2BX221EX2DX2264X2DI__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 14, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _HERE__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 4);
                link(mem, cal_4 + 0, Var(lam_0));
                link(mem, cal_4 + 1, Var(lam_1));
                link(mem, cal_4 + 2, Var(lam_2));
                link(mem, cal_4 + 3, Var(lam_3));
                link(mem, lam_3 + 1, Cal(4, 37, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__6_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 7);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, ask_arg(mem, term, 3));
                link(mem, cal_1 + 4, ask_arg(mem, term, 4));
                link(mem, cal_1 + 5, ask_arg(mem, term, 5));
                link(mem, cal_1 + 6, Var(lam_0));
                link(mem, lam_0 + 1, Cal(7, 47, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 6);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2C____2_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 2);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                u64 done = Ctr(2, 191, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _HERE__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 37, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _NODE__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                u64 done = Ctr(3, 184, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__SPLIT__E__5_: {
              if (get_tag(ask_arg(mem,term,4)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 4), 4);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 137u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 3);
                link(mem, cal_4 + 0, Ctr(0, 5, ctr_2));
                link(mem, cal_4 + 1, Ctr(0, 5, ctr_3));
                link(mem, cal_4 + 2, ask_arg(mem, ask_arg(mem, term, 4), 2));
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_5 + 2, Cal(3, 41, cal_4));
                u64 done = Cal(3, 67, cal_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 1));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 139u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_3 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_3 + 2, Ctr(0, 5, ctr_2));
                u64 done = Cal(3, 9, cal_3);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 1));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 2));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 141u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 3);
                link(mem, cal_4 + 0, Ctr(0, 5, ctr_2));
                link(mem, cal_4 + 1, Ctr(0, 5, ctr_3));
                link(mem, cal_4 + 2, ask_arg(mem, ask_arg(mem, term, 4), 2));
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_5 + 2, Cal(3, 41, cal_4));
                u64 done = Cal(3, 105, cal_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 1));
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DX5BX5DX221E__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 69, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _NODE__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 45, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _LESS__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 67, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _SUC__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 129, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2BX221EX2DX2264__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 214, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__D__3_: {
              if (1) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 1)) == U32 && get_tag(U_32(1)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 1)) - get_val(U_32(1)));
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 1));
                  link(mem, op2_1 + 1, U_32(1));
                  ret_0 = Op2(SUB, op2_1);
                }
                u64 done = ret_0;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              break;
            };
            case _CONG__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DDEC__SPLIT__A__3_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 39, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Cal(3, 142, cal_0));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 2, Ctr(0, 5, ctr_4));
                u64 cal_6 = alloc(mem, 3);
                link(mem, cal_6 + 0, Ctr(0, 5, ctr_1));
                link(mem, cal_6 + 1, Ctr(0, 5, ctr_2));
                link(mem, cal_6 + 2, Cal(3, 58, cal_5));
                u64 done = Cal(3, 41, cal_6);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _IF__3_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 32u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 33u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _ORD_CONSTRUCTOR__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 4);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, Var(lam_0));
                link(mem, cal_3 + 2, Var(lam_1));
                link(mem, cal_3 + 3, Var(lam_2));
                link(mem, lam_2 + 1, Cal(4, 71, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPMAYBE__4_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 4);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                u64 done = Cal(4, 178, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _GT__2_: {
              if (1) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 0)) == U32 && get_tag(ask_arg(mem, term, 1)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 0)) >  get_val(ask_arg(mem, term, 1)) ? 1 : 0);
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 0));
                  link(mem, op2_1 + 1, ask_arg(mem, term, 1));
                  ret_0 = Op2(GTN, op2_1);
                }
                u64 cal_2 = alloc(mem, 1);
                link(mem, cal_2 + 0, ret_0);
                u64 done = Cal(1, 235, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINR__5_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 5);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                link(mem, cal_0 + 4, ask_arg(mem, term, 4));
                u64 done = Cal(5, 88, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPMAYBE__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 65, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DDEC__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 58, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DREFL__SPLIT__C__3_: {
              if (get_tag(ask_arg(mem,term,2)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 2), 2);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 173u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 114, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 24u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 2);
                link(mem, ctr_2 + 0, ask_arg(mem, term, 1));
                link(mem, ctr_2 + 1, ask_arg(mem, ask_arg(mem, term, 2), 0));
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_3 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_3 + 2, Ctr(2, 174, ctr_2));
                u64 done = Cal(3, 106, cal_3);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 62u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 75, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264X2DI__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 87, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__M__11_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 4));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 8));
                u64 done = Ctr(3, 18, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 11);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 7));
                collect(mem, ask_arg(mem, term, 9));
                collect(mem, ask_arg(mem, term, 10));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DANTISYM__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FLATTEN__4_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 5);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, ask_arg(mem, term, 3));
                link(mem, cal_1 + 4, Var(lam_0));
                link(mem, lam_0 + 1, Cal(5, 121, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _FROMLIST__3_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 done = Cal(3, 242, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _NODE__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 45, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2C____0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 126, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINR__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 5);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 2));
                link(mem, cal_2 + 3, Var(lam_0));
                link(mem, cal_2 + 4, Var(lam_1));
                link(mem, lam_1 + 1, Cal(5, 94, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _EQUAL__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                u64 done = Ctr(3, 139, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__SPLIT__A__2_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 2);
                link(mem, cal_0 + 0, U_32(0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                u64 done = Cal(2, 150, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, term, 1);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = ask_arg(mem, term, 0);
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 cal_10 = alloc(mem, 2);
                link(mem, cal_10 + 0, dp0_6);
                link(mem, cal_10 + 1, dp0_1);
                u64 cal_11 = alloc(mem, 3);
                link(mem, cal_11 + 0, dp1_7);
                link(mem, cal_11 + 1, dp1_2);
                link(mem, cal_11 + 2, Cal(2, 188, cal_10));
                u64 done = Cal(3, 198, cal_11);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _IT__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 12, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__5_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 6);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, ask_arg(mem, term, 3));
                link(mem, cal_1 + 4, ask_arg(mem, term, 4));
                link(mem, cal_1 + 5, Var(lam_0));
                link(mem, lam_0 + 1, Cal(6, 20, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _X2DX221EX2DX2264X2DI__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 27, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FLATTEN__5_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 5);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                link(mem, cal_0 + 4, ask_arg(mem, term, 4));
                u64 done = Cal(5, 183, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__G__13_: {
              if (get_tag(ask_arg(mem,term,6)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 6), 6);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 6)) == CTR && get_ext(ask_arg(mem, term, 6)) == 107u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 6), 2);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = ask_arg(mem, ask_arg(mem, term, 6), 1);
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 6), 0);
                u64 dp0_11;
                u64 dp1_12;
                if (get_tag(cpy_10) == U32) {
                  inc_cost(mem);
                  dp0_11 = cpy_10;
                  dp1_12 = cpy_10;
                } else {
                  u64 dup_13 = alloc(mem, 3);
                  u64 col_14 = gen_dupk(mem);
                  link(mem, dup_13 + 2, cpy_10);
                  dp0_11 = Dp0(col_14, dup_13);
                  dp1_12 = Dp1(col_14, dup_13);
                }
                u64 ctr_15 = alloc(mem, 3);
                link(mem, ctr_15 + 0, dp0_11);
                link(mem, ctr_15 + 1, dp0_6);
                link(mem, ctr_15 + 2, dp0_1);
                u64 cal_16 = alloc(mem, 16);
                link(mem, cal_16 + 0, ask_arg(mem, term, 0));
                link(mem, cal_16 + 1, ask_arg(mem, term, 1));
                link(mem, cal_16 + 2, ask_arg(mem, term, 2));
                link(mem, cal_16 + 3, ask_arg(mem, term, 3));
                link(mem, cal_16 + 4, ask_arg(mem, term, 4));
                link(mem, cal_16 + 5, ask_arg(mem, term, 5));
                link(mem, cal_16 + 6, Ctr(3, 107, ctr_15));
                link(mem, cal_16 + 7, ask_arg(mem, term, 7));
                link(mem, cal_16 + 8, ask_arg(mem, term, 8));
                link(mem, cal_16 + 9, ask_arg(mem, term, 9));
                link(mem, cal_16 + 10, ask_arg(mem, term, 10));
                link(mem, cal_16 + 11, ask_arg(mem, term, 11));
                link(mem, cal_16 + 12, ask_arg(mem, term, 12));
                link(mem, cal_16 + 13, dp1_12);
                link(mem, cal_16 + 14, dp1_7);
                link(mem, cal_16 + 15, dp1_2);
                u64 done = Cal(16, 213, cal_16);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 13);
                clear(mem, get_loc(ask_arg(mem, term, 6), 0), 3);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 6)) == CTR && get_ext(ask_arg(mem, term, 6)) == 214u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 75, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 13);
                clear(mem, get_loc(ask_arg(mem, term, 6), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 6), 0));
                collect(mem, ask_arg(mem, term, 7));
                collect(mem, ask_arg(mem, term, 8));
                collect(mem, ask_arg(mem, term, 9));
                collect(mem, ask_arg(mem, term, 10));
                collect(mem, ask_arg(mem, term, 11));
                collect(mem, ask_arg(mem, term, 12));
                init = 1;
                continue;
              }
              break;
            };
            case _X2DX221EX2DX2264__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 222, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 cal_5 = alloc(mem, 8);
                link(mem, cal_5 + 0, ask_arg(mem, term, 0));
                link(mem, cal_5 + 1, ask_arg(mem, term, 1));
                link(mem, cal_5 + 2, ask_arg(mem, term, 2));
                link(mem, cal_5 + 3, Var(lam_0));
                link(mem, cal_5 + 4, Var(lam_1));
                link(mem, cal_5 + 5, Var(lam_2));
                link(mem, cal_5 + 6, Var(lam_3));
                link(mem, cal_5 + 7, Var(lam_4));
                link(mem, lam_4 + 1, Cal(8, 7, cal_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264X2DI__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 87, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DA__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 253, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TDO_CONSTRUCTOR__2_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 2);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                u64 done = Ctr(2, 109, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINL__5_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 5);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                link(mem, cal_0 + 4, ask_arg(mem, term, 4));
                u64 done = Cal(5, 144, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__8_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 8);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                link(mem, cal_0 + 4, ask_arg(mem, term, 4));
                link(mem, cal_0 + 5, ask_arg(mem, term, 5));
                link(mem, cal_0 + 6, ask_arg(mem, term, 6));
                link(mem, cal_0 + 7, ask_arg(mem, term, 7));
                u64 done = Cal(8, 229, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 8);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DREFL__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 11, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _SO__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _INL__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 1, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _ZERO__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 168, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DSUC__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                u64 done = Ctr(3, 156, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _JUST__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 140, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _INR__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 90, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _GREATER__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 105, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINR__SPLIT__E__5_: {
              if (get_tag(ask_arg(mem,term,4)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 4), 4);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 89u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, ask_arg(mem, term, 4), 0));
                u64 done = Ctr(1, 89, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 90u)) {
                inc_cost(mem);
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, ask_arg(mem, term, 3));
                link(mem, app_0 + 1, ask_arg(mem, ask_arg(mem, term, 4), 0));
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, App(app_0));
                u64 done = Cal(1, 91, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              break;
            };
            case _SND__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 191u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, ask_arg(mem, term, 0), 1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 2);
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 0));
                init = 1;
                continue;
              }
              break;
            };
            case _SUBST__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 6);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, ask_arg(mem, term, 1));
                link(mem, cal_3 + 2, ask_arg(mem, term, 2));
                link(mem, cal_3 + 3, Var(lam_0));
                link(mem, cal_3 + 4, Var(lam_1));
                link(mem, cal_3 + 5, Var(lam_2));
                link(mem, lam_2 + 1, Cal(6, 3, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINR__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 5);
                link(mem, cal_4 + 0, ask_arg(mem, term, 0));
                link(mem, cal_4 + 1, Var(lam_0));
                link(mem, cal_4 + 2, Var(lam_1));
                link(mem, cal_4 + 3, Var(lam_2));
                link(mem, cal_4 + 4, Var(lam_3));
                link(mem, lam_3 + 1, Cal(5, 94, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _NODE__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 45, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _X2DX221EX2DX2264X2DI__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 27, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _GREATER__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                u64 done = Ctr(3, 141, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DZERO__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 39, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FROMLIST__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 117, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__5_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 5);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                link(mem, cal_0 + 4, ask_arg(mem, term, 4));
                u64 done = Cal(5, 175, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _FROMLIST__SPLIT__C__3_: {
              if (get_tag(ask_arg(mem,term,2)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 2), 2);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 22u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 cal_2 = alloc(mem, 1);
                link(mem, cal_2 + 0, Cal(1, 114, cal_1));
                u64 done = Cal(1, 48, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 218u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, term, 1);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 ctr_5 = alloc(mem, 0);
                u64 ctr_6 = alloc(mem, 0);
                u64 ctr_7 = alloc(mem, 0);
                u64 ctr_8 = alloc(mem, 0);
                u64 cal_9 = alloc(mem, 3);
                link(mem, cal_9 + 0, Ctr(0, 5, ctr_8));
                link(mem, cal_9 + 1, dp1_2);
                link(mem, cal_9 + 2, ask_arg(mem, ask_arg(mem, term, 2), 1));
                u64 ctr_10 = alloc(mem, 0);
                u64 cal_11 = alloc(mem, 1);
                link(mem, cal_11 + 0, Ctr(0, 5, ctr_10));
                u64 ctr_12 = alloc(mem, 0);
                u64 cal_13 = alloc(mem, 1);
                link(mem, cal_13 + 0, Ctr(0, 5, ctr_12));
                u64 cal_14 = alloc(mem, 8);
                link(mem, cal_14 + 0, Ctr(0, 5, ctr_5));
                link(mem, cal_14 + 1, dp0_1);
                link(mem, cal_14 + 2, Ctr(0, 5, ctr_6));
                link(mem, cal_14 + 3, Ctr(0, 5, ctr_7));
                link(mem, cal_14 + 4, ask_arg(mem, ask_arg(mem, term, 2), 0));
                link(mem, cal_14 + 5, Cal(3, 117, cal_9));
                link(mem, cal_14 + 6, Cal(1, 114, cal_11));
                link(mem, cal_14 + 7, Cal(1, 75, cal_13));
                u64 done = Cal(8, 7, cal_14);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264X2DI__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 4);
                link(mem, cal_4 + 0, Var(lam_0));
                link(mem, cal_4 + 1, Var(lam_1));
                link(mem, cal_4 + 2, Var(lam_2));
                link(mem, cal_4 + 3, Var(lam_3));
                link(mem, lam_3 + 1, Cal(4, 87, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DZERO__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 54, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ORD_CONSTRUCTOR__4_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 4);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                link(mem, ctr_0 + 3, ask_arg(mem, term, 3));
                u64 done = Ctr(4, 43, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _EQ__2_: {
              if (1) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 0)) == U32 && get_tag(ask_arg(mem, term, 1)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 0)) == get_val(ask_arg(mem, term, 1)) ? 1 : 0);
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 0));
                  link(mem, op2_1 + 1, ask_arg(mem, term, 1));
                  ret_0 = Op2(EQL, op2_1);
                }
                u64 cal_2 = alloc(mem, 1);
                link(mem, cal_2 + 0, ret_0);
                u64 done = Cal(1, 85, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINL__SPLIT__E__5_: {
              if (get_tag(ask_arg(mem,term,4)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 4), 4);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 89u)) {
                inc_cost(mem);
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, ask_arg(mem, term, 3));
                link(mem, app_0 + 1, ask_arg(mem, ask_arg(mem, term, 4), 0));
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, App(app_0));
                u64 done = Cal(1, 1, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 90u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, ask_arg(mem, term, 4), 0));
                u64 done = Ctr(1, 90, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 1);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__C__2_: {
              if (1) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 0)) == U32 && get_tag(U_32(1)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 0)) - get_val(U_32(1)));
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 0));
                  link(mem, op2_1 + 1, U_32(1));
                  ret_0 = Op2(SUB, op2_1);
                }
                u64 done = ret_0;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _SND__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 190, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TESTFLATTEN__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 5);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_5 + 2, Ctr(0, 5, ctr_2));
                link(mem, cal_5 + 3, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 4, Cal(0, 111, cal_4));
                u64 done = Cal(5, 121, cal_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LEFT__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 51, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _X5B__X5D__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 77, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _INL__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 89, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 6);
                link(mem, cal_4 + 0, ask_arg(mem, term, 0));
                link(mem, cal_4 + 1, ask_arg(mem, term, 1));
                link(mem, cal_4 + 2, Var(lam_0));
                link(mem, cal_4 + 3, Var(lam_1));
                link(mem, cal_4 + 4, Var(lam_2));
                link(mem, cal_4 + 5, Var(lam_3));
                link(mem, lam_3 + 1, Cal(6, 20, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _X2BX221EX2DX2264X2DI__2_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 75, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2237____2_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 2);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                u64 done = Ctr(2, 218, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _TESTLOOKUP__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 6);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_5 + 1, Cal(0, 112, cal_1));
                link(mem, cal_5 + 2, Ctr(0, 5, ctr_2));
                link(mem, cal_5 + 3, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 4, U_32(3));
                link(mem, cal_5 + 5, Cal(0, 113, cal_4));
                u64 done = Cal(6, 20, cal_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINR__4_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 5);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, ask_arg(mem, term, 3));
                link(mem, cal_1 + 4, Var(lam_0));
                link(mem, lam_0 + 1, Cal(5, 94, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _EQ__SPLIT__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 1u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 32, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 33, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINL__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 5);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 2));
                link(mem, cal_2 + 3, Var(lam_0));
                link(mem, cal_2 + 4, Var(lam_1));
                link(mem, lam_1 + 1, Cal(5, 16, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__SPLIT__K__10_: {
              if (get_tag(ask_arg(mem,term,9)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 9), 9);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 9)) == CTR && get_ext(ask_arg(mem, term, 9)) == 137u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_2));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 2, Ctr(0, 5, ctr_4));
                u64 ctr_6 = alloc(mem, 0);
                u64 ctr_7 = alloc(mem, 0);
                u64 ctr_8 = alloc(mem, 0);
                u64 cal_9 = alloc(mem, 6);
                link(mem, cal_9 + 0, Ctr(0, 5, ctr_6));
                link(mem, cal_9 + 1, ask_arg(mem, term, 1));
                link(mem, cal_9 + 2, Ctr(0, 5, ctr_7));
                link(mem, cal_9 + 3, Ctr(0, 5, ctr_8));
                link(mem, cal_9 + 4, ask_arg(mem, term, 4));
                link(mem, cal_9 + 5, ask_arg(mem, term, 7));
                u64 cal_10 = alloc(mem, 4);
                link(mem, cal_10 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_10 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_10 + 2, Cal(3, 138, cal_5));
                link(mem, cal_10 + 3, Cal(6, 20, cal_9));
                u64 done = Cal(4, 65, cal_10);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 10);
                clear(mem, get_loc(ask_arg(mem, term, 9), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 8));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 1));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 2));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 9)) == CTR && get_ext(ask_arg(mem, term, 9)) == 139u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 4);
                link(mem, cal_4 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_4 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_4 + 2, Ctr(0, 5, ctr_2));
                link(mem, cal_4 + 3, Ctr(0, 5, ctr_3));
                u64 cal_5 = alloc(mem, 1);
                link(mem, cal_5 + 0, Cal(4, 37, cal_4));
                u64 done = Cal(1, 140, cal_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 10);
                clear(mem, get_loc(ask_arg(mem, term, 9), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 7));
                collect(mem, ask_arg(mem, term, 8));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 1));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 2));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 9)) == CTR && get_ext(ask_arg(mem, term, 9)) == 141u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 3);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_2));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 2, Ctr(0, 5, ctr_4));
                u64 ctr_6 = alloc(mem, 0);
                u64 ctr_7 = alloc(mem, 0);
                u64 ctr_8 = alloc(mem, 0);
                u64 cal_9 = alloc(mem, 6);
                link(mem, cal_9 + 0, Ctr(0, 5, ctr_6));
                link(mem, cal_9 + 1, ask_arg(mem, term, 1));
                link(mem, cal_9 + 2, Ctr(0, 5, ctr_7));
                link(mem, cal_9 + 3, Ctr(0, 5, ctr_8));
                link(mem, cal_9 + 4, ask_arg(mem, term, 4));
                link(mem, cal_9 + 5, ask_arg(mem, term, 8));
                u64 cal_10 = alloc(mem, 4);
                link(mem, cal_10 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_10 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_10 + 2, Cal(3, 73, cal_5));
                link(mem, cal_10 + 3, Cal(6, 20, cal_9));
                u64 done = Cal(4, 65, cal_10);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 10);
                clear(mem, get_loc(ask_arg(mem, term, 9), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 7));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 1));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 9), 2));
                init = 1;
                continue;
              }
              break;
            };
            case _FROMLIST__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 117, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _HERE__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 37, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _HERE__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 4);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, Var(lam_0));
                link(mem, cal_3 + 2, Var(lam_1));
                link(mem, cal_3 + 3, Var(lam_2));
                link(mem, lam_2 + 1, Cal(4, 37, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__4_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 5);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, ask_arg(mem, term, 3));
                link(mem, cal_1 + 4, Var(lam_0));
                link(mem, lam_0 + 1, Cal(5, 96, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DREFL__B__1_: {
              if (1) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 0)) == U32 && get_tag(U_32(1)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 0)) - get_val(U_32(1)));
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 0));
                  link(mem, op2_1 + 1, U_32(1));
                  ret_0 = Op2(SUB, op2_1);
                }
                u64 done = ret_0;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _SYM__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 lam_5 = alloc(mem, 2);
                u64 cal_6 = alloc(mem, 7);
                link(mem, cal_6 + 0, ask_arg(mem, term, 0));
                link(mem, cal_6 + 1, Var(lam_0));
                link(mem, cal_6 + 2, Var(lam_1));
                link(mem, cal_6 + 3, Var(lam_2));
                link(mem, cal_6 + 4, Var(lam_3));
                link(mem, cal_6 + 5, Var(lam_4));
                link(mem, cal_6 + 6, Var(lam_5));
                link(mem, lam_5 + 1, Cal(7, 47, cal_6));
                link(mem, lam_4 + 1, Lam(lam_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DX5BX5DX221E__3_: {
              if (1) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, term, 1);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 ctr_5 = alloc(mem, 0);
                u64 lam_6 = alloc(mem, 2);
                u64 ctr_7 = alloc(mem, 0);
                u64 cal_8 = alloc(mem, 3);
                link(mem, cal_8 + 0, Ctr(0, 5, ctr_7));
                link(mem, cal_8 + 1, dp0_1);
                link(mem, cal_8 + 2, Var(lam_6));
                link(mem, lam_6 + 1, Cal(3, 11, cal_8));
                u64 lam_9 = alloc(mem, 2);
                u64 lam_10 = alloc(mem, 2);
                u64 lam_11 = alloc(mem, 2);
                u64 ctr_12 = alloc(mem, 0);
                u64 cal_13 = alloc(mem, 5);
                link(mem, cal_13 + 0, Ctr(0, 5, ctr_12));
                link(mem, cal_13 + 1, dp1_2);
                link(mem, cal_13 + 2, Var(lam_9));
                link(mem, cal_13 + 3, Var(lam_10));
                link(mem, cal_13 + 4, Var(lam_11));
                link(mem, lam_11 + 1, Cal(5, 78, cal_13));
                link(mem, lam_10 + 1, Lam(lam_11));
                link(mem, lam_9 + 1, Lam(lam_10));
                u64 ctr_14 = alloc(mem, 0);
                u64 cal_15 = alloc(mem, 4);
                link(mem, cal_15 + 0, Ctr(0, 5, ctr_5));
                link(mem, cal_15 + 1, Lam(lam_6));
                link(mem, cal_15 + 2, Lam(lam_9));
                link(mem, cal_15 + 3, Ctr(0, 5, ctr_14));
                u64 done = Cal(4, 71, cal_15);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              break;
            };
            case _LESS__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 67, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__2_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 2);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                u64 done = Cal(2, 53, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DNAT__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 1);
                link(mem, cal_2 + 0, Var(lam_1));
                link(mem, lam_1 + 1, Cal(1, 42, cal_2));
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 lam_5 = alloc(mem, 2);
                u64 ctr_6 = alloc(mem, 0);
                u64 ctr_7 = alloc(mem, 0);
                u64 ctr_8 = alloc(mem, 0);
                u64 cal_9 = alloc(mem, 3);
                link(mem, cal_9 + 0, Ctr(0, 5, ctr_6));
                link(mem, cal_9 + 1, Ctr(0, 5, ctr_7));
                link(mem, cal_9 + 2, Ctr(0, 5, ctr_8));
                link(mem, lam_5 + 0, Era());
                link(mem, lam_5 + 1, Cal(3, 72, cal_9));
                link(mem, lam_4 + 0, Era());
                link(mem, lam_4 + 1, Lam(lam_5));
                link(mem, lam_3 + 0, Era());
                link(mem, lam_3 + 1, Lam(lam_4));
                u64 ctr_10 = alloc(mem, 0);
                u64 cal_11 = alloc(mem, 4);
                link(mem, cal_11 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_11 + 1, Lam(lam_1));
                link(mem, cal_11 + 2, Lam(lam_3));
                link(mem, cal_11 + 3, Ctr(0, 5, ctr_10));
                u64 done = Cal(4, 71, cal_11);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MONUS__2_: {
              if (1) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, term, 1);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 cpy_5 = ask_arg(mem, term, 0);
                u64 dp0_6;
                u64 dp1_7;
                if (get_tag(cpy_5) == U32) {
                  inc_cost(mem);
                  dp0_6 = cpy_5;
                  dp1_7 = cpy_5;
                } else {
                  u64 dup_8 = alloc(mem, 3);
                  u64 col_9 = gen_dupk(mem);
                  link(mem, dup_8 + 2, cpy_5);
                  dp0_6 = Dp0(col_9, dup_8);
                  dp1_7 = Dp1(col_9, dup_8);
                }
                u64 ret_10;
                if (get_tag(dp0_6) == U32 && get_tag(dp0_1) == U32) {
                  ret_10 = U_32(get_val(dp0_6) >  get_val(dp0_1) ? 1 : 0);
                  inc_cost(mem);
                } else {
                  u64 op2_11 = alloc(mem, 2);
                  link(mem, op2_11 + 0, dp0_6);
                  link(mem, op2_11 + 1, dp0_1);
                  ret_10 = Op2(GTN, op2_11);
                }
                u64 cal_12 = alloc(mem, 3);
                link(mem, cal_12 + 0, ret_10);
                link(mem, cal_12 + 1, dp1_7);
                link(mem, cal_12 + 2, dp1_2);
                u64 done = Cal(3, 176, cal_12);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__5_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 7);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 2));
                link(mem, cal_2 + 3, ask_arg(mem, term, 3));
                link(mem, cal_2 + 4, ask_arg(mem, term, 4));
                link(mem, cal_2 + 5, Var(lam_0));
                link(mem, cal_2 + 6, Var(lam_1));
                link(mem, lam_1 + 1, Cal(7, 47, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _GT__SPLIT__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 1u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 32, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 33, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ORD_CONSTRUCTOR__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 71, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _RIGHT__4_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 4);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                link(mem, ctr_0 + 3, ask_arg(mem, term, 3));
                u64 done = Ctr(4, 219, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _RIGHT__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 35, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _SND__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 158, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FST__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 191u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, ask_arg(mem, term, 0), 0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 2);
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 1));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DREFL__3_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 done = Cal(3, 172, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _X2DX221EX2DX2264X2DI__2_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 done = Cal(1, 114, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _SUBST__5_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 6);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, ask_arg(mem, term, 3));
                link(mem, cal_1 + 4, ask_arg(mem, term, 4));
                link(mem, cal_1 + 5, Var(lam_0));
                link(mem, lam_0 + 1, Cal(6, 3, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DDEC__3_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 done = Cal(3, 268, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _TRI__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 109u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, ask_arg(mem, term, 0), 1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 2);
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 0));
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 106, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 cal_5 = alloc(mem, 5);
                link(mem, cal_5 + 0, Var(lam_0));
                link(mem, cal_5 + 1, Var(lam_1));
                link(mem, cal_5 + 2, Var(lam_2));
                link(mem, cal_5 + 3, Var(lam_3));
                link(mem, cal_5 + 4, Var(lam_4));
                link(mem, lam_4 + 1, Cal(5, 96, cal_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 102, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DREFL__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 38, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 38, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _GREATER__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 105, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__6_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 6);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                link(mem, cal_0 + 4, ask_arg(mem, term, 4));
                link(mem, cal_0 + 5, ask_arg(mem, term, 5));
                u64 done = Cal(6, 123, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 6);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 52, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 cal_5 = alloc(mem, 7);
                link(mem, cal_5 + 0, ask_arg(mem, term, 0));
                link(mem, cal_5 + 1, ask_arg(mem, term, 1));
                link(mem, cal_5 + 2, Var(lam_0));
                link(mem, cal_5 + 3, Var(lam_1));
                link(mem, cal_5 + 4, Var(lam_2));
                link(mem, cal_5 + 5, Var(lam_3));
                link(mem, cal_5 + 6, Var(lam_4));
                link(mem, lam_4 + 1, Cal(7, 47, cal_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DX22A4__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 4);
                link(mem, cal_4 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_4 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_4 + 2, Ctr(0, 5, ctr_2));
                link(mem, cal_4 + 3, Ctr(0, 5, ctr_3));
                u64 done = Cal(4, 71, cal_4);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 lam_5 = alloc(mem, 2);
                u64 cal_6 = alloc(mem, 8);
                link(mem, cal_6 + 0, ask_arg(mem, term, 0));
                link(mem, cal_6 + 1, ask_arg(mem, term, 1));
                link(mem, cal_6 + 2, Var(lam_0));
                link(mem, cal_6 + 3, Var(lam_1));
                link(mem, cal_6 + 4, Var(lam_2));
                link(mem, cal_6 + 5, Var(lam_3));
                link(mem, cal_6 + 6, Var(lam_4));
                link(mem, cal_6 + 7, Var(lam_5));
                link(mem, lam_5 + 1, Cal(8, 7, cal_6));
                link(mem, lam_4 + 1, Lam(lam_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _LEAF__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 48, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__4_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 8);
                link(mem, cal_4 + 0, ask_arg(mem, term, 0));
                link(mem, cal_4 + 1, ask_arg(mem, term, 1));
                link(mem, cal_4 + 2, ask_arg(mem, term, 2));
                link(mem, cal_4 + 3, ask_arg(mem, term, 3));
                link(mem, cal_4 + 4, Var(lam_0));
                link(mem, cal_4 + 5, Var(lam_1));
                link(mem, cal_4 + 6, Var(lam_2));
                link(mem, cal_4 + 7, Var(lam_3));
                link(mem, lam_3 + 1, Cal(8, 7, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _SUBST__6_: {
              if (1) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 6);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                init = 1;
                continue;
              }
              break;
            };
            case _TESTINSERT__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 0);
                u64 ctr_5 = alloc(mem, 0);
                u64 cal_6 = alloc(mem, 1);
                link(mem, cal_6 + 0, Ctr(0, 5, ctr_5));
                u64 ctr_7 = alloc(mem, 0);
                u64 cal_8 = alloc(mem, 1);
                link(mem, cal_8 + 0, Ctr(0, 5, ctr_7));
                u64 cal_9 = alloc(mem, 8);
                link(mem, cal_9 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_9 + 1, Cal(0, 112, cal_1));
                link(mem, cal_9 + 2, Ctr(0, 5, ctr_2));
                link(mem, cal_9 + 3, Ctr(0, 5, ctr_3));
                link(mem, cal_9 + 4, U_32(4));
                link(mem, cal_9 + 5, Cal(0, 113, cal_4));
                link(mem, cal_9 + 6, Cal(1, 114, cal_6));
                link(mem, cal_9 + 7, Cal(1, 75, cal_8));
                u64 done = Cal(8, 7, cal_9);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LOOKUP__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 cal_5 = alloc(mem, 6);
                link(mem, cal_5 + 0, ask_arg(mem, term, 0));
                link(mem, cal_5 + 1, Var(lam_0));
                link(mem, cal_5 + 2, Var(lam_1));
                link(mem, cal_5 + 3, Var(lam_2));
                link(mem, cal_5 + 4, Var(lam_3));
                link(mem, cal_5 + 5, Var(lam_4));
                link(mem, lam_4 + 1, Cal(6, 20, cal_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINL__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 5);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, ask_arg(mem, term, 1));
                link(mem, cal_3 + 2, Var(lam_0));
                link(mem, cal_3 + 3, Var(lam_1));
                link(mem, cal_3 + 4, Var(lam_2));
                link(mem, lam_2 + 1, Cal(5, 16, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _MAIN_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 83, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DREFL__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 11, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _SUBST__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 lam_5 = alloc(mem, 2);
                u64 cal_6 = alloc(mem, 6);
                link(mem, cal_6 + 0, Var(lam_0));
                link(mem, cal_6 + 1, Var(lam_1));
                link(mem, cal_6 + 2, Var(lam_2));
                link(mem, cal_6 + 3, Var(lam_3));
                link(mem, cal_6 + 4, Var(lam_4));
                link(mem, cal_6 + 5, Var(lam_5));
                link(mem, lam_5 + 1, Cal(6, 3, cal_6));
                link(mem, lam_4 + 1, Lam(lam_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPINR__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 cal_5 = alloc(mem, 5);
                link(mem, cal_5 + 0, Var(lam_0));
                link(mem, cal_5 + 1, Var(lam_1));
                link(mem, cal_5 + 2, Var(lam_2));
                link(mem, cal_5 + 3, Var(lam_3));
                link(mem, cal_5 + 4, Var(lam_4));
                link(mem, lam_4 + 1, Cal(5, 94, cal_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _RIGHT__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 4);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, Var(lam_0));
                link(mem, cal_3 + 2, Var(lam_1));
                link(mem, cal_3 + 3, Var(lam_2));
                link(mem, lam_2 + 1, Cal(4, 35, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _SORT__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 80, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _FLATTEN__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 5);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 2));
                link(mem, cal_2 + 3, Var(lam_0));
                link(mem, cal_2 + 4, Var(lam_1));
                link(mem, lam_1 + 1, Cal(5, 121, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _TRI__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 246, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 5);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 2));
                link(mem, cal_2 + 3, Var(lam_0));
                link(mem, cal_2 + 4, Var(lam_1));
                link(mem, lam_1 + 1, Cal(5, 96, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _FST__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 55, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2BX2B____3_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 done = Cal(3, 208, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _TRINAT__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 52, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DTRANS__SPLIT__E__8_: {
              if (get_tag(ask_arg(mem,term,4)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 4), 4);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 156u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 ctr_2 = alloc(mem, 0);
                u64 ctr_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 5);
                link(mem, cal_5 + 0, Ctr(0, 5, ctr_2));
                link(mem, cal_5 + 1, Ctr(0, 5, ctr_3));
                link(mem, cal_5 + 2, Ctr(0, 5, ctr_4));
                link(mem, cal_5 + 3, ask_arg(mem, term, 7));
                link(mem, cal_5 + 4, ask_arg(mem, ask_arg(mem, term, 4), 2));
                u64 cal_6 = alloc(mem, 3);
                link(mem, cal_6 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_6 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_6 + 2, Cal(5, 96, cal_5));
                u64 done = Cal(3, 41, cal_6);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 8);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 0));
                collect(mem, ask_arg(mem, ask_arg(mem, term, 4), 1));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                init = 1;
                continue;
              }
              break;
            };
            case _TT__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 101, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__SPLIT__D__12_: {
              if (get_tag(ask_arg(mem,term,3)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 3), 3);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 3)) == CTR && get_ext(ask_arg(mem, term, 3)) == 24u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 3), 0);
                u64 dp0_1;
                u64 dp1_2;
                if (get_tag(cpy_0) == U32) {
                  inc_cost(mem);
                  dp0_1 = cpy_0;
                  dp1_2 = cpy_0;
                } else {
                  u64 dup_3 = alloc(mem, 3);
                  u64 col_4 = gen_dupk(mem);
                  link(mem, dup_3 + 2, cpy_0);
                  dp0_1 = Dp0(col_4, dup_3);
                  dp1_2 = Dp1(col_4, dup_3);
                }
                u64 ctr_5 = alloc(mem, 1);
                link(mem, ctr_5 + 0, dp0_1);
                u64 cal_6 = alloc(mem, 13);
                link(mem, cal_6 + 0, ask_arg(mem, term, 0));
                link(mem, cal_6 + 1, ask_arg(mem, term, 1));
                link(mem, cal_6 + 2, ask_arg(mem, term, 2));
                link(mem, cal_6 + 3, Ctr(1, 24, ctr_5));
                link(mem, cal_6 + 4, ask_arg(mem, term, 4));
                link(mem, cal_6 + 5, ask_arg(mem, term, 5));
                link(mem, cal_6 + 6, ask_arg(mem, term, 6));
                link(mem, cal_6 + 7, ask_arg(mem, term, 7));
                link(mem, cal_6 + 8, ask_arg(mem, term, 8));
                link(mem, cal_6 + 9, ask_arg(mem, term, 9));
                link(mem, cal_6 + 10, ask_arg(mem, term, 10));
                link(mem, cal_6 + 11, ask_arg(mem, term, 11));
                link(mem, cal_6 + 12, dp1_2);
                u64 done = Cal(13, 25, cal_6);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 12);
                clear(mem, get_loc(ask_arg(mem, term, 3), 0), 1);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 7);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 12);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                collect(mem, ask_arg(mem, term, 4));
                collect(mem, ask_arg(mem, term, 5));
                collect(mem, ask_arg(mem, term, 6));
                collect(mem, ask_arg(mem, term, 8));
                collect(mem, ask_arg(mem, term, 9));
                collect(mem, ask_arg(mem, term, 10));
                collect(mem, ask_arg(mem, term, 11));
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2BX2B____0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 161, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _RIGHT__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 4);
                link(mem, cal_4 + 0, Var(lam_0));
                link(mem, cal_4 + 1, Var(lam_1));
                link(mem, cal_4 + 2, Var(lam_2));
                link(mem, cal_4 + 3, Var(lam_3));
                link(mem, lam_3 + 1, Cal(4, 35, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LEFT__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 4);
                link(mem, cal_4 + 0, Var(lam_0));
                link(mem, cal_4 + 1, Var(lam_1));
                link(mem, cal_4 + 2, Var(lam_2));
                link(mem, cal_4 + 3, Var(lam_3));
                link(mem, lam_3 + 1, Cal(4, 51, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LT__SPLIT__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 1u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 32, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 33, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2BX2B____2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 161, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 lam_5 = alloc(mem, 2);
                u64 lam_6 = alloc(mem, 2);
                u64 cal_7 = alloc(mem, 8);
                link(mem, cal_7 + 0, ask_arg(mem, term, 0));
                link(mem, cal_7 + 1, Var(lam_0));
                link(mem, cal_7 + 2, Var(lam_1));
                link(mem, cal_7 + 3, Var(lam_2));
                link(mem, cal_7 + 4, Var(lam_3));
                link(mem, cal_7 + 5, Var(lam_4));
                link(mem, cal_7 + 6, Var(lam_5));
                link(mem, cal_7 + 7, Var(lam_6));
                link(mem, lam_6 + 1, Cal(8, 7, cal_7));
                link(mem, lam_5 + 1, Lam(lam_6));
                link(mem, lam_4 + 1, Lam(lam_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TDO_CONSTRUCTOR__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 165, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2C____1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 126, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DA__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 109u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, ask_arg(mem, term, 0), 0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 2);
                collect(mem, ask_arg(mem, ask_arg(mem, term, 0), 1));
                init = 1;
                continue;
              }
              break;
            };
            case _EQUAL__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 9, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 106, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _MAPMAYBE__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 4);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, Var(lam_0));
                link(mem, cal_3 + 2, Var(lam_1));
                link(mem, cal_3 + 3, Var(lam_2));
                link(mem, lam_2 + 1, Cal(4, 65, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _GREATER__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 105, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DDEC__D__3_: {
              if (1) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 0)) == U32 && get_tag(U_32(1)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 0)) - get_val(U_32(1)));
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 0));
                  link(mem, op2_1 + 1, U_32(1));
                  ret_0 = Op2(SUB, op2_1);
                }
                u64 done = ret_0;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              break;
            };
            case _TESTMAPMAYBE__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 lam_2 = alloc(mem, 2);
                u64 ret_3;
                if (get_tag(U_32(1)) == U32 && get_tag(Var(lam_2)) == U32) {
                  ret_3 = U_32(get_val(U_32(1)) + get_val(Var(lam_2)));
                  inc_cost(mem);
                } else {
                  u64 op2_4 = alloc(mem, 2);
                  link(mem, op2_4 + 0, U_32(1));
                  link(mem, op2_4 + 1, Var(lam_2));
                  ret_3 = Op2(ADD, op2_4);
                }
                link(mem, lam_2 + 1, ret_3);
                u64 cal_5 = alloc(mem, 1);
                link(mem, cal_5 + 0, U_32(5));
                u64 cal_6 = alloc(mem, 4);
                link(mem, cal_6 + 0, Ctr(0, 5, ctr_0));
                link(mem, cal_6 + 1, Ctr(0, 5, ctr_1));
                link(mem, cal_6 + 2, Lam(lam_2));
                link(mem, cal_6 + 3, Cal(1, 140, cal_5));
                u64 done = Cal(4, 65, cal_6);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LEFT__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 51, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _FLATTEN__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 lam_4 = alloc(mem, 2);
                u64 cal_5 = alloc(mem, 5);
                link(mem, cal_5 + 0, Var(lam_0));
                link(mem, cal_5 + 1, Var(lam_1));
                link(mem, cal_5 + 2, Var(lam_2));
                link(mem, cal_5 + 3, Var(lam_3));
                link(mem, cal_5 + 4, Var(lam_4));
                link(mem, lam_4 + 1, Cal(5, 121, cal_5));
                link(mem, lam_3 + 1, Lam(lam_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _ORDX2DA__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 224, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TRI__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 108, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2BX2B____1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 161, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DDEC__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 58, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TESTTRINAT__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 2);
                link(mem, cal_0 + 0, U_32(3));
                link(mem, cal_0 + 1, U_32(5));
                u64 done = Cal(2, 52, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _SUC__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 220, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2237____1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 118, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TRANS__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 5, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DREFL__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 42, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 42, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _LESS__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                u64 done = Ctr(3, 137, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _LEFT__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 4);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, Var(lam_0));
                link(mem, cal_3 + 2, Var(lam_1));
                link(mem, cal_3 + 3, Var(lam_2));
                link(mem, lam_2 + 1, Cal(4, 51, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX221EX2DTRANS__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 lam_3 = alloc(mem, 2);
                u64 cal_4 = alloc(mem, 7);
                link(mem, cal_4 + 0, ask_arg(mem, term, 0));
                link(mem, cal_4 + 1, ask_arg(mem, term, 1));
                link(mem, cal_4 + 2, ask_arg(mem, term, 2));
                link(mem, cal_4 + 3, Var(lam_0));
                link(mem, cal_4 + 4, Var(lam_1));
                link(mem, cal_4 + 5, Var(lam_2));
                link(mem, cal_4 + 6, Var(lam_3));
                link(mem, lam_3 + 1, Cal(7, 47, cal_4));
                link(mem, lam_2 + 1, Lam(lam_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _RIGHT__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 35, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _MAIN__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 166, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2BX221EX2DX2264__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 75, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X2DX221E__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 173, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FLATTEN__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 5);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, ask_arg(mem, term, 1));
                link(mem, cal_3 + 2, Var(lam_0));
                link(mem, cal_3 + 3, Var(lam_1));
                link(mem, cal_3 + 4, Var(lam_2));
                link(mem, lam_2 + 1, Cal(5, 121, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _TESTBST__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Ctr(0, 5, ctr_0));
                u64 cal_2 = alloc(mem, 1);
                link(mem, cal_2 + 0, Cal(1, 114, cal_1));
                u64 ctr_3 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 1);
                link(mem, cal_4 + 0, Ctr(0, 5, ctr_3));
                u64 cal_5 = alloc(mem, 1);
                link(mem, cal_5 + 0, Cal(1, 75, cal_4));
                u64 cal_6 = alloc(mem, 3);
                link(mem, cal_6 + 0, U_32(3));
                link(mem, cal_6 + 1, Cal(1, 48, cal_2));
                link(mem, cal_6 + 2, Cal(1, 48, cal_5));
                u64 done = Cal(3, 45, cal_6);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _INSERT__6_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 8);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, ask_arg(mem, term, 2));
                link(mem, cal_2 + 3, ask_arg(mem, term, 3));
                link(mem, cal_2 + 4, ask_arg(mem, term, 4));
                link(mem, cal_2 + 5, ask_arg(mem, term, 5));
                link(mem, cal_2 + 6, Var(lam_0));
                link(mem, cal_2 + 7, Var(lam_1));
                link(mem, lam_1 + 1, Cal(8, 7, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 6);
                init = 1;
                continue;
              }
              break;
            };
            case _X2264X2DSUC__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 41, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _X5BX5DX2DX2264X2DI__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 4);
                link(mem, cal_3 + 0, ask_arg(mem, term, 0));
                link(mem, cal_3 + 1, Var(lam_0));
                link(mem, cal_3 + 2, Var(lam_1));
                link(mem, cal_3 + 3, Var(lam_2));
                link(mem, lam_2 + 1, Cal(4, 87, cal_3));
                link(mem, lam_1 + 1, Lam(lam_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };

          }
          //GENERATED_REWRITE_RULES_STEP_1_END//

          break;
        }
      }
    }

    u64 item = stk_pop(&stack);
    if (item == -1) {
      break;
    } else {
      init = item >> 31;
      host = item & 0x7FFFFFFF;
      continue;
    }

  }

  return ask_lnk(mem, root);
}

// sets the nth bit of a bit-array represented as a u64 array
void set_bit(u64* bits, u64 bit) {
  bits[bit >> 6] |= (1ULL << (bit & 0x3f));
}

// gets the nth bit of a bit-array represented as a u64 array
u8 get_bit(u64* bits, u64 bit) {
  return (bits[bit >> 6] >> (bit & 0x3F)) & 1;
}

#ifdef PARALLEL
void normal_fork(u64 tid, u64 host, u64 sidx, u64 slen);
u64  normal_join(u64 tid);
#endif

u64 normal_seen_data[NORMAL_SEEN_MCAP];

void normal_init(void) {
  for (u64 i = 0; i < NORMAL_SEEN_MCAP; ++i) {
    normal_seen_data[i] = 0;
  }
}

Lnk normal_go(Worker* mem, u64 host, u64 sidx, u64 slen) {
  Lnk term = ask_lnk(mem, host);
  //printf("normal %llu %llu | ", sidx, slen); debug_print_lnk(term); printf("\n");
  if (get_bit(normal_seen_data, host)) {
    return term;
  } else {
    term = reduce(mem, host, slen);
    set_bit(normal_seen_data, host);
    u64 rec_size = 0;
    u64 rec_locs[16];
    switch (get_tag(term)) {
      case LAM: {
        rec_locs[rec_size++] = get_loc(term,1);
        break;
      }
      case APP: {
        rec_locs[rec_size++] = get_loc(term,0);
        rec_locs[rec_size++] = get_loc(term,1);
        break;
      }
      case PAR: {
        rec_locs[rec_size++] = get_loc(term,0);
        rec_locs[rec_size++] = get_loc(term,1);
        break;
      }
      case DP0: {
        rec_locs[rec_size++] = get_loc(term,2);
        break;
      }
      case DP1: {
        rec_locs[rec_size++] = get_loc(term,2);
        break;
      }
      case OP2: {
        if (slen > 1) {
          rec_locs[rec_size++] = get_loc(term,0);
          rec_locs[rec_size++] = get_loc(term,1);
          break;
        }
      }
      case CTR: case CAL: {
        u64 arity = (u64)get_ari(term);
        for (u64 i = 0; i < arity; ++i) {
          rec_locs[rec_size++] = get_loc(term,i);
        }
        break;
      }
    }
    #ifdef PARALLEL

    //printf("ue %llu %llu\n", rec_size, slen);

    if (rec_size >= 2 && slen >= rec_size) {

      u64 space = slen / rec_size;

      for (u64 i = 1; i < rec_size; ++i) {
        //printf("spawn %llu %llu\n", sidx + i * space, space);
        normal_fork(sidx + i * space, rec_locs[i], sidx + i * space, space);
      }

      link(mem, rec_locs[0], normal_go(mem, rec_locs[0], sidx, space));

      for (u64 i = 1; i < rec_size; ++i) {
        link(mem, get_loc(term, i), normal_join(sidx + i * space));
      }

    } else {

      for (u64 i = 0; i < rec_size; ++i) {
        link(mem, rec_locs[i], normal_go(mem, rec_locs[i], sidx, slen));
      }

    }
    #else

    for (u64 i = 0; i < rec_size; ++i) {
      link(mem, rec_locs[i], normal_go(mem, rec_locs[i], sidx, slen));
    }

    #endif

    return term;
  }
}

Lnk normal(Worker* mem, u64 host, u64 sidx, u64 slen) {
  // In order to allow parallelization of numeric operations, reduce() will treat OP2 as a CTR if
  // there is enough thread space. So, for example, normalizing a recursive "sum" function with 4
  // threads might return something like `(+ (+ 64 64) (+ 64 64))`. reduce() will treat the first
  // 2 layers as CTRs, allowing normal() to parallelize them. So, in order to finish the reduction,
  // we call `normal_go()` a second time, with no thread space, to eliminate lasting redexes.
  normal_init();
  normal_go(mem, host, sidx, slen);
  u64 done;
  u64 cost = mem->cost;
  while (1) {
    normal_init();
    done = normal_go(mem, host, 0, 1);
    if (mem->cost != cost) {
      cost = mem->cost;
    } else {
      break;
    }
  }
  return done;
}


#ifdef PARALLEL

// Normalizes in a separate thread
// Note that, right now, the allocator will just partition the space of the
// normal form equally among threads, which will not fully use the CPU cores in
// many cases. A better task scheduler should be implemented. See Issues.
void normal_fork(u64 tid, u64 host, u64 sidx, u64 slen) {
  pthread_mutex_lock(&workers[tid].has_work_mutex);
  workers[tid].has_work = (sidx << 48) | (slen << 32) | host;
  pthread_cond_signal(&workers[tid].has_work_signal);
  pthread_mutex_unlock(&workers[tid].has_work_mutex);
}

// Waits the result of a forked normalizer
u64 normal_join(u64 tid) {
  while (1) {
    pthread_mutex_lock(&workers[tid].has_result_mutex);
    while (workers[tid].has_result == -1) {
      pthread_cond_wait(&workers[tid].has_result_signal, &workers[tid].has_result_mutex);
    }
    u64 done = workers[tid].has_result;
    workers[tid].has_result = -1;
    pthread_mutex_unlock(&workers[tid].has_result_mutex);
    return done;
  }
}

// Stops a worker
void worker_stop(u64 tid) {
  pthread_mutex_lock(&workers[tid].has_work_mutex);
  workers[tid].has_work = -2;
  pthread_cond_signal(&workers[tid].has_work_signal);
  pthread_mutex_unlock(&workers[tid].has_work_mutex);
}

// The normalizer worker
void *worker(void *arg) {
  u64 tid = (u64)arg;
  while (1) {
    pthread_mutex_lock(&workers[tid].has_work_mutex);
    while (workers[tid].has_work == -1) {
      pthread_cond_wait(&workers[tid].has_work_signal, &workers[tid].has_work_mutex);
    }
    u64 work = workers[tid].has_work;
    if (work == -2) {
      break;
    } else {
      u64 sidx = (work >> 48) & 0xFFFF;
      u64 slen = (work >> 32) & 0xFFFF;
      u64 host = (work >>  0) & 0xFFFFFFFF;
      workers[tid].has_result = normal_go(&workers[tid], host, sidx, slen);
      workers[tid].has_work = -1;
      pthread_cond_signal(&workers[tid].has_result_signal);
      pthread_mutex_unlock(&workers[tid].has_work_mutex);
    }
  }
  return 0;
}

#endif

u64 ffi_cost;
u64 ffi_size;

void ffi_normal(u8* mem_data, u32 mem_size, u32 host) {

  // Init thread objects
  for (u64 t = 0; t < MAX_WORKERS; ++t) {
    workers[t].tid = t;
    workers[t].size = t == 0 ? (u64)mem_size : 0l;
    workers[t].node = (u64*)mem_data;
    for (u64 a = 0; a < MAX_ARITY; ++a) {
      stk_init(&workers[t].free[a]);
    }
    workers[t].cost = 0;
    workers[t].dups = MAX_DUPS * t / MAX_WORKERS;
    #ifdef PARALLEL
    workers[t].has_work = -1;
    pthread_mutex_init(&workers[t].has_work_mutex, NULL);
    pthread_cond_init(&workers[t].has_work_signal, NULL);
    workers[t].has_result = -1;
    pthread_mutex_init(&workers[t].has_result_mutex, NULL);
    pthread_cond_init(&workers[t].has_result_signal, NULL);
    // workers[t].thread = NULL;
    #endif
  }

  // Spawns threads
  #ifdef PARALLEL
  for (u64 tid = 1; tid < MAX_WORKERS; ++tid) {
    pthread_create(&workers[tid].thread, NULL, &worker, (void*)tid);
  }
  #endif

  // Normalizes trm
  normal(&workers[0], (u64) host, 0, MAX_WORKERS);

  // Computes total cost and size
  ffi_cost = 0;
  ffi_size = 0;
  for (u64 tid = 0; tid < MAX_WORKERS; ++tid) {
    ffi_cost += workers[tid].cost;
    ffi_size += workers[tid].size;
  }

  #ifdef PARALLEL

  // Asks workers to stop
  for (u64 tid = 1; tid < MAX_WORKERS; ++tid) {
    worker_stop(tid);
  }

  // Waits workers to stop
  for (u64 tid = 1; tid < MAX_WORKERS; ++tid) {
    pthread_join(workers[tid].thread, NULL);
  }

  #endif

  // Clears workers
  for (u64 tid = 0; tid < MAX_WORKERS; ++tid) {
    for (u64 a = 0; a < MAX_ARITY; ++a) {
      stk_free(&workers[tid].free[a]);
    }
    #ifdef PARALLEL
    pthread_mutex_destroy(&workers[tid].has_work_mutex);
    pthread_cond_destroy(&workers[tid].has_work_signal);
    pthread_mutex_destroy(&workers[tid].has_result_mutex);
    pthread_cond_destroy(&workers[tid].has_result_signal);
    #endif
  }
}

// Readback
// --------

void readback_vars(Stk* vars, Worker* mem, Lnk term, Stk* seen) {
  //printf("- readback_vars %llu ", get_loc(term,0)); debug_print_lnk(term); printf("\n");
  if (stk_find(seen, term) != -1) { // FIXME: probably very slow, change to a proper hashmap
    return;
  } else {
    stk_push(seen, term);
    switch (get_tag(term)) {
      case LAM: {
        u64 argm = ask_arg(mem, term, 0);
        u64 body = ask_arg(mem, term, 1);
        if (get_tag(argm) != ERA) {
          stk_push(vars, Var(get_loc(term, 0)));
        };
        readback_vars(vars, mem, body, seen);
        break;
      }
      case APP: {
        u64 lam = ask_arg(mem, term, 0);
        u64 arg = ask_arg(mem, term, 1);
        readback_vars(vars, mem, lam, seen);
        readback_vars(vars, mem, arg, seen);
        break;
      }
      case PAR: {
        u64 arg0 = ask_arg(mem, term, 0);
        u64 arg1 = ask_arg(mem, term, 1);
        readback_vars(vars, mem, arg0, seen);
        readback_vars(vars, mem, arg1, seen);
        break;
      }
      case DP0: {
        u64 arg = ask_arg(mem, term, 2);
        readback_vars(vars, mem, arg, seen);
        break;
      }
      case DP1: {
        u64 arg = ask_arg(mem, term, 2);
        readback_vars(vars, mem, arg, seen);
        break;
      }
      case OP2: {
        u64 arg0 = ask_arg(mem, term, 0);
        u64 arg1 = ask_arg(mem, term, 1);
        readback_vars(vars, mem, arg0, seen);
        readback_vars(vars, mem, arg1, seen);
        break;
      }
      case CTR: case CAL: {
        u64 arity = get_ari(term);
        for (u64 i = 0; i < arity; ++i) {
          readback_vars(vars, mem, ask_arg(mem, term, i), seen);
        }
        break;
      }
    }
  }
}

void readback_decimal_go(Stk* chrs, u64 n) {
  //printf("--- A %llu\n", n);
  if (n > 0) {
    readback_decimal_go(chrs, n / 10);
    stk_push(chrs, '0' + (n % 10));
  }
}

void readback_decimal(Stk* chrs, u64 n) {
  if (n == 0) {
    stk_push(chrs, '0');
  } else {
    readback_decimal_go(chrs, n);
  }
}

void readback_term(Stk* chrs, Worker* mem, Lnk term, Stk* vars, Stk* dirs, char** id_to_name_data, u64 id_to_name_mcap) {
  //printf("- readback_term: "); debug_print_lnk(term); printf("\n");
  switch (get_tag(term)) {
    case LAM: {
      stk_push(chrs, '@');
      if (get_tag(ask_arg(mem, term, 0)) == ERA) {
        stk_push(chrs, '_');
      } else {
        stk_push(chrs, 'x');
        readback_decimal(chrs, stk_find(vars, Var(get_loc(term, 0))));
      };
      stk_push(chrs, ' ');
      readback_term(chrs, mem, ask_arg(mem, term, 1), vars, dirs, id_to_name_data, id_to_name_mcap);
      break;
    }
    case APP: {
      stk_push(chrs, '(');
      readback_term(chrs, mem, ask_arg(mem, term, 0), vars, dirs, id_to_name_data, id_to_name_mcap);
      stk_push(chrs, ' ');
      readback_term(chrs, mem, ask_arg(mem, term, 1), vars, dirs, id_to_name_data, id_to_name_mcap);
      stk_push(chrs, ')');
      break;
    }
    case PAR: {
      u64 col = get_ext(term);
      if (dirs[col].size > 0) {
        u64 head = stk_pop(&dirs[col]);
        if (head == 0) {
          readback_term(chrs, mem, ask_arg(mem, term, 0), vars, dirs, id_to_name_data, id_to_name_mcap);
          stk_push(&dirs[col], head);
        } else {
          readback_term(chrs, mem, ask_arg(mem, term, 1), vars, dirs, id_to_name_data, id_to_name_mcap);
          stk_push(&dirs[col], head);
        }
      } else {
        stk_push(chrs, '<');
        readback_term(chrs, mem, ask_arg(mem, term, 0), vars, dirs, id_to_name_data, id_to_name_mcap);
        stk_push(chrs, ' ');
        readback_term(chrs, mem, ask_arg(mem, term, 1), vars, dirs, id_to_name_data, id_to_name_mcap);
        stk_push(chrs, '>');
      }
      break;
    }
    case DP0: case DP1: {
      u64 col = get_ext(term);
      u64 val = ask_arg(mem, term, 2);
      stk_push(&dirs[col], get_tag(term) == DP0 ? 0 : 1);
      readback_term(chrs, mem, ask_arg(mem, term, 2), vars, dirs, id_to_name_data, id_to_name_mcap);
      stk_pop(&dirs[col]);
      break;
    }
    case OP2: {
      stk_push(chrs, '(');
      readback_term(chrs, mem, ask_arg(mem, term, 0), vars, dirs, id_to_name_data, id_to_name_mcap);
      switch (get_ext(term)) {
        case ADD: { stk_push(chrs, '+'); break; }
        case SUB: { stk_push(chrs, '-'); break; }
        case MUL: { stk_push(chrs, '*'); break; }
        case DIV: { stk_push(chrs, '/'); break; }
        case MOD: { stk_push(chrs, '%'); break; }
        case AND: { stk_push(chrs, '&'); break; }
        case OR: { stk_push(chrs, '|'); break; }
        case XOR: { stk_push(chrs, '^'); break; }
        case SHL: { stk_push(chrs, '<'); stk_push(chrs, '<'); break; }
        case SHR: { stk_push(chrs, '>'); stk_push(chrs, '>'); break; }
        case LTN: { stk_push(chrs, '<'); break; }
        case LTE: { stk_push(chrs, '<'); stk_push(chrs, '='); break; }
        case EQL: { stk_push(chrs, '='); stk_push(chrs, '='); break; }
        case GTE: { stk_push(chrs, '>'); stk_push(chrs, '='); break; }
        case GTN: { stk_push(chrs, '>'); break; }
        case NEQ: { stk_push(chrs, '!'); stk_push(chrs, '='); break; }
      }
      readback_term(chrs, mem, ask_arg(mem, term, 1), vars, dirs, id_to_name_data, id_to_name_mcap);
      stk_push(chrs, ')');
      break;
    }
    case U32: {
      //printf("- u32\n");
      readback_decimal(chrs, get_val(term));
      //printf("- u32 done\n");
      break;
    }
    case CTR: case CAL: {
      u64 func = get_ext(term);
      u64 arit = get_ari(term);
      stk_push(chrs, '(');
      if (func < id_to_name_mcap && id_to_name_data[func] != NULL) {
        for (u64 i = 0; id_to_name_data[func][i] != '\0'; ++i) {
          stk_push(chrs, id_to_name_data[func][i]);
        }
      } else {
        stk_push(chrs, '$');
        readback_decimal(chrs, func); // TODO: function names
      }
      for (u64 i = 0; i < arit; ++i) {
        stk_push(chrs, ' ');
        readback_term(chrs, mem, ask_arg(mem, term, i), vars, dirs, id_to_name_data, id_to_name_mcap);
      }
      stk_push(chrs, ')');
      break;
    }
    case VAR: {
      stk_push(chrs, 'x');
      readback_decimal(chrs, stk_find(vars, term));
      break;
    }
    default: {
      stk_push(chrs, '?');
      break;
    }
  }
}

void readback(char* code_data, u64 code_mcap, Worker* mem, Lnk term, char** id_to_name_data, u64 id_to_name_mcap) {
  //printf("reading back\n");

  // Used vars
  Stk seen;
  Stk chrs;
  Stk vars;
  Stk* dirs;

  // Initialization
  stk_init(&seen);
  stk_init(&chrs);
  stk_init(&vars);
  dirs = (Stk*)malloc(sizeof(Stk) * DIRS_MCAP);
  assert(dirs);
  for (u64 i = 0; i < DIRS_MCAP; ++i) {
    stk_init(&dirs[i]);
  }

  // Readback
  readback_vars(&vars, mem, term, &seen);
  readback_term(&chrs, mem, term, &vars, dirs, id_to_name_data, id_to_name_mcap);

  // Generates C string
  for (u64 i = 0; i < chrs.size && i < code_mcap; ++i) {
    code_data[i] = chrs.data[i];
  }
  code_data[chrs.size < code_mcap ? chrs.size : code_mcap] = '\0';

  // Cleanup
  stk_free(&seen);
  stk_free(&chrs);
  stk_free(&vars);
  for (u64 i = 0; i < DIRS_MCAP; ++i) {
    stk_free(&dirs[i]);
  }
}

// Debug
// -----

void debug_print_lnk(Lnk x) {
  u64 tag = get_tag(x);
  u64 ext = get_ext(x);
  u64 val = get_val(x);
  switch (tag) {
    case DP0: printf("DP0"); break;
    case DP1: printf("DP1"); break;
    case VAR: printf("VAR"); break;
    case ARG: printf("ARG"); break;
    case ERA: printf("ERA"); break;
    case LAM: printf("LAM"); break;
    case APP: printf("APP"); break;
    case PAR: printf("PAR"); break;
    case CTR: printf("CTR"); break;
    case CAL: printf("CAL"); break;
    case OP2: printf("OP2"); break;
    case U32: printf("U32"); break;
    case F32: printf("F32"); break;
    case NIL: printf("NIL"); break;
    default : printf("???"); break;
  }
  printf(":%"PRIx64":%"PRIx64"", ext, val);
}

// Main
// ----

Lnk parse_arg(char* code, char** id_to_name_data, u64 id_to_name_size) {
  if (code[0] >= '0' && code[0] <= '9') {
    return U_32(strtol(code, 0, 10));
  } else {
    return U_32(0);
  }
}

// Uncomment to test without Deno FFI
int main(int argc, char* argv[]) {

  Worker mem;
  struct timeval stop, start;

  // Id-to-Name map
  const u64 id_to_name_size = 295;
  char* id_to_name_data[id_to_name_size];
  id_to_name_data[63] = "X2264x2Dsuc_2";
  id_to_name_data[155] = "X2264x2Dtrans_split_e_8";
  id_to_name_data[103] = "X2264x2Dtrans_split_a_1";
  id_to_name_data[85] = "Eq_split_1";
  id_to_name_data[171] = "Sym_0";
  id_to_name_data[183] = "Flatten_split_e_5";
  id_to_name_data[294] = "Lookup_0";
  id_to_name_data[32] = "True";
  id_to_name_data[96] = "X2264x2Dtrans_5";
  id_to_name_data[192] = "Monus_2";
  id_to_name_data[39] = "X2264x2Dzero_1";
  id_to_name_data[22] = "X5Bx5D";
  id_to_name_data[269] = "Ordx2DA_0";
  id_to_name_data[278] = "Subst_4";
  id_to_name_data[133] = "X2264x2Drefl_0";
  id_to_name_data[55] = "Fst_1";
  id_to_name_data[216] = "Lookup_3";
  id_to_name_data[180] = "Nothing";
  id_to_name_data[21] = "X5Bx5D_0";
  id_to_name_data[57] = "X2264x2Ddec_2";
  id_to_name_data[93] = "MapInr_2";
  id_to_name_data[201] = "TriNat_split_e_5";
  id_to_name_data[161] = "Z_x2Bx2B__3";
  id_to_name_data[148] = "TriNat_0";
  id_to_name_data[159] = "Right_1";
  id_to_name_data[149] = "Ordx2Dx22A4_0";
  id_to_name_data[71] = "Ord.constructor_4";
  id_to_name_data[18] = "Tri_3";
  id_to_name_data[158] = "Snd_1";
  id_to_name_data[258] = "X2264x2Dzero_0";
  id_to_name_data[101] = "Tt";
  id_to_name_data[141] = "Greater";
  id_to_name_data[248] = "Z_x2237__1";
  id_to_name_data[33] = "False";
  id_to_name_data[130] = "Z_x2264__0";
  id_to_name_data[140] = "Just_1";
  id_to_name_data[45] = "Node_3";
  id_to_name_data[167] = "Zero_0";
  id_to_name_data[256] = "So_0";
  id_to_name_data[13] = "X2Bx221Ex2Dx2264x2DI_1";
  id_to_name_data[14] = "X2Bx221Ex2Dx2264x2DI_2";
  id_to_name_data[89] = "Inl";
  id_to_name_data[139] = "Equal";
  id_to_name_data[24] = "X5B_x5D";
  id_to_name_data[166] = "Test1_0";
  id_to_name_data[61] = "X2Bx221E_0";
  id_to_name_data[128] = "Suc_0";
  id_to_name_data[127] = "Node_1";
  id_to_name_data[226] = "Z_x2237__0";
  id_to_name_data[181] = "Here_3";
  id_to_name_data[70] = "Ordx2DNat_0";
  id_to_name_data[178] = "MapMaybe_split_d_4";
  id_to_name_data[237] = "Left_0";
  id_to_name_data[129] = "Suc_1";
  id_to_name_data[69] = "Ordx2Dx5Bx5Dx221E_3";
  id_to_name_data[86] = "X5Bx5Dx2Dx2264x2DI_3";
  id_to_name_data[113] = "TestBST_0";
  id_to_name_data[79] = "Sort_1";
  id_to_name_data[125] = "Z_x2C__0";
  id_to_name_data[236] = "Subst_3";
  id_to_name_data[241] = "X5Bx5Dx221Ex2Dtrans_6";
  id_to_name_data[265] = "X2264x2Ddec_0";
  id_to_name_data[285] = "Insert_m_11";
  id_to_name_data[157] = "Snd_0";
  id_to_name_data[288] = "Ord.constructor_2";
  id_to_name_data[173] = "X2Dx221E";
  id_to_name_data[151] = "MapMaybe_3";
  id_to_name_data[26] = "X2Dx221Ex2Dx2264x2DI_0";
  id_to_name_data[72] = "X2264x2Dtrans_3";
  id_to_name_data[262] = "Insert_0";
  id_to_name_data[172] = "X5Bx5Dx221Ex2Drefl_split_c_3";
  id_to_name_data[73] = "Right_3";
  id_to_name_data[1] = "Inl_1";
  id_to_name_data[255] = "Just_0";
  id_to_name_data[62] = "X2Bx221E";
  id_to_name_data[274] = "Flatten_4";
  id_to_name_data[117] = "FromList_3";
  id_to_name_data[245] = "Tri_0";
  id_to_name_data[244] = "X5Bx5Dx221Ex2Dtrans_0";
  id_to_name_data[76] = "X5B_x5D_0";
  id_to_name_data[162] = "Ord.constructor_1";
  id_to_name_data[66] = "Less_2";
  id_to_name_data[97] = "Right_2";
  id_to_name_data[108] = "Tri_split_a_1";
  id_to_name_data[2] = "Subst_2";
  id_to_name_data[64] = "MapMaybe_1";
  id_to_name_data[213] = "X5Bx5Dx221Ex2Dtrans_split_e_16";
  id_to_name_data[210] = "X5Bx5Dx221Ex2Dtrans_h_7";
  id_to_name_data[81] = "X2264x2Dsuc_1";
  id_to_name_data[235] = "Gt_split_1";
  id_to_name_data[292] = "Refl_0";
  id_to_name_data[136] = "Lookup_split_k_10";
  id_to_name_data[49] = "Leaf";
  id_to_name_data[50] = "Left_2";
  id_to_name_data[84] = "Left_1";
  id_to_name_data[102] = "X2264x2Dtrans_1";
  id_to_name_data[165] = "TDO.constructor_2";
  id_to_name_data[230] = "Subst_1";
  id_to_name_data[137] = "Less";
  id_to_name_data[150] = "TriNat_split_b_2";
  id_to_name_data[5] = "Erased";
  id_to_name_data[198] = "TriNat_split_b_3";
  id_to_name_data[9] = "Equal_3";
  id_to_name_data[92] = "Insert_4";
  id_to_name_data[99] = "X5Bx5Dx221Ex2Dtrans_2";
  id_to_name_data[119] = "It_1";
  id_to_name_data[25] = "X5Bx5Dx221Ex2Dtrans_split_g_13";
  id_to_name_data[211] = "X5Bx5Dx221Ex2Dtrans_split_f_8";
  id_to_name_data[209] = "X5Bx5Dx2Dx2264_1";
  id_to_name_data[286] = "X5Bx5Dx221Ex2Dtrans_3";
  id_to_name_data[174] = "X2264x2Drefl_2";
  id_to_name_data[233] = "Insert_3";
  id_to_name_data[272] = "Eq_2";
  id_to_name_data[6] = "Insert_7";
  id_to_name_data[132] = "Here_2";
  id_to_name_data[7] = "Insert_8";
  id_to_name_data[23] = "X5Bx5Dx221Ex2Dtrans_split_d_12";
  id_to_name_data[40] = "X2264x2Drefl_b_1";
  id_to_name_data[227] = "Insert_6";
  id_to_name_data[231] = "Insert_2";
  id_to_name_data[124] = "MapInl_4";
  id_to_name_data[131] = "Equal_1";
  id_to_name_data[91] = "Inr_1";
  id_to_name_data[179] = "Just";
  id_to_name_data[120] = "Flatten_2";
  id_to_name_data[143] = "MapInr_1";
  id_to_name_data[142] = "X2264x2Ddec_d_3";
  id_to_name_data[194] = "Ord.constructor_3";
  id_to_name_data[234] = "TDO.constructor_1";
  id_to_name_data[164] = "Fst_0";
  id_to_name_data[263] = "Flatten_1";
  id_to_name_data[4] = "X2264x2Dantisym_0";
  id_to_name_data[77] = "X5B_x5D_1";
  id_to_name_data[182] = "Flatten_0";
  id_to_name_data[47] = "X5Bx5Dx221Ex2Dtrans_7";
  id_to_name_data[74] = "X2Bx221Ex2Dx2264_0";
  id_to_name_data[104] = "Greater_2";
  id_to_name_data[280] = "TestFlatten_0";
  id_to_name_data[52] = "TriNat_2";
  id_to_name_data[38] = "X2264x2Drefl_split_a_1";
  id_to_name_data[224] = "Ordx2DA_split_a_1";
  id_to_name_data[252] = "X5Bx5Dx2Dx2264_0";
  id_to_name_data[260] = "Here";
  id_to_name_data[220] = "Suc";
  id_to_name_data[215] = "Here_1";
  id_to_name_data[251] = "Subst_5";
  id_to_name_data[112] = "TDOx2DNat_0";
  id_to_name_data[261] = "X2264x2Dtrans_0";
  id_to_name_data[169] = "X5Bx5Dx2Dx2264x2DI_1";
  id_to_name_data[199] = "TriNat_d_3";
  id_to_name_data[175] = "X2264x2Dtrans_split_d_5";
  id_to_name_data[168] = "Zero";
  id_to_name_data[240] = "Z_x2Bx2B__1";
  id_to_name_data[94] = "MapInr_5";
  id_to_name_data[239] = "Lt_split_1";
  id_to_name_data[144] = "MapInl_split_e_5";
  id_to_name_data[247] = "FromList_0";
  id_to_name_data[281] = "X5Bx5Dx2Dx2264x2DI_2";
  id_to_name_data[15] = "MapInl_1";
  id_to_name_data[196] = "Z_x2C__1";
  id_to_name_data[250] = "Greater_0";
  id_to_name_data[60] = "Lookup_1";
  id_to_name_data[253] = "Ordx2DA_1";
  id_to_name_data[232] = "X2264x2Dsuc_0";
  id_to_name_data[268] = "X2264x2Ddec_split_a_3";
  id_to_name_data[156] = "X2264x2Dsuc";
  id_to_name_data[37] = "Here_4";
  id_to_name_data[284] = "MapInl_3";
  id_to_name_data[36] = "Here_0";
  id_to_name_data[214] = "X2Bx221Ex2Dx2264";
  id_to_name_data[28] = "XAC__0";
  id_to_name_data[82] = "Main";
  id_to_name_data[135] = "X5Bx5Dx221Ex2Dantisym_0";
  id_to_name_data[146] = "Inr_0";
  id_to_name_data[195] = "TDO.constructor_0";
  id_to_name_data[43] = "Ord.constructor";
  id_to_name_data[67] = "Less_3";
  id_to_name_data[0] = "Inl_0";
  id_to_name_data[44] = "Node_0";
  id_to_name_data[187] = "Equal_2";
  id_to_name_data[111] = "TestInsert_0";
  id_to_name_data[188] = "TriNat_c_2";
  id_to_name_data[217] = "Sort_0";
  id_to_name_data[204] = "Flatten_3";
  id_to_name_data[212] = "X2Dx221E_0";
  id_to_name_data[185] = "Insert_split_m_12";
  id_to_name_data[114] = "X2Dx221Ex2Dx2264_1";
  id_to_name_data[123] = "Lookup_split_f_6";
  id_to_name_data[17] = "Lookup_k_9";
  id_to_name_data[106] = "X5Bx5Dx2Dx2264_3";
  id_to_name_data[197] = "TestMapMaybe_0";
  id_to_name_data[75] = "X2Bx221Ex2Dx2264_1";
  id_to_name_data[116] = "TestFromList_0";
  id_to_name_data[107] = "X5Bx5Dx2Dx2264";
  id_to_name_data[126] = "Z_x2C__2";
  id_to_name_data[207] = "MapInr_3";
  id_to_name_data[186] = "X2264x2Ddec_1";
  id_to_name_data[218] = "Z_x2237_";
  id_to_name_data[153] = "X5Bx5Dx2Dx2264_2";
  id_to_name_data[42] = "X2264x2Drefl_1";
  id_to_name_data[78] = "X5Bx5Dx221Ex2Dtrans_5";
  id_to_name_data[190] = "Snd_split_a_1";
  id_to_name_data[270] = "Insert_1";
  id_to_name_data[68] = "Ordx2Dx5Bx5Dx221E_2";
  id_to_name_data[53] = "TriNat_split_a_2";
  id_to_name_data[271] = "MapInr_4";
  id_to_name_data[20] = "Lookup_6";
  id_to_name_data[276] = "MapMaybe_0";
  id_to_name_data[8] = "Equal_0";
  id_to_name_data[264] = "Lookup_5";
  id_to_name_data[283] = "False_0";
  id_to_name_data[54] = "X2264x2Dzero";
  id_to_name_data[88] = "MapInr_split_e_5";
  id_to_name_data[90] = "Inr";
  id_to_name_data[19] = "Lookup_2";
  id_to_name_data[208] = "Z_x2Bx2B__split_b_3";
  id_to_name_data[163] = "TestLookup_0";
  id_to_name_data[200] = "TriNat_e_4";
  id_to_name_data[154] = "X2Bx221Ex2Dx2264x2DI_0";
  id_to_name_data[228] = "TestTriNat_0";
  id_to_name_data[98] = "Leaf_0";
  id_to_name_data[170] = "Z_x2265__0";
  id_to_name_data[266] = "Trans_0";
  id_to_name_data[12] = "It_2";
  id_to_name_data[229] = "Insert_split_f_8";
  id_to_name_data[254] = "Ordx2Dx5Bx5Dx221E_0";
  id_to_name_data[257] = "It_0";
  id_to_name_data[259] = "Nothing_0";
  id_to_name_data[221] = "X5Bx5Dx221Ex2Dtrans_4";
  id_to_name_data[95] = "X2264x2Dtrans_4";
  id_to_name_data[267] = "Ordx2Dx5Bx5Dx221E_1";
  id_to_name_data[30] = "X2Dx221Ex2Dx2264x2DI_1";
  id_to_name_data[225] = "X2264x2Dtrans_2";
  id_to_name_data[273] = "MapMaybe_2";
  id_to_name_data[11] = "X5Bx5Dx221Ex2Drefl_3";
  id_to_name_data[193] = "FromList_1";
  id_to_name_data[118] = "Z_x2237__2";
  id_to_name_data[121] = "Flatten_5";
  id_to_name_data[203] = "Cong_0";
  id_to_name_data[242] = "FromList_split_c_3";
  id_to_name_data[122] = "Less_0";
  id_to_name_data[59] = "X5Bx5Dx221Ex2Drefl_2";
  id_to_name_data[289] = "X5Bx5Dx2Dx2264x2DI_0";
  id_to_name_data[202] = "True_0";
  id_to_name_data[246] = "Tri_1";
  id_to_name_data[105] = "Greater_3";
  id_to_name_data[275] = "Subst_0";
  id_to_name_data[191] = "Z_x2C_";
  id_to_name_data[279] = "Gt_2";
  id_to_name_data[290] = "FromList_2";
  id_to_name_data[291] = "X2264x2Dtrans_6";
  id_to_name_data[134] = "Sort_2";
  id_to_name_data[51] = "Left_4";
  id_to_name_data[205] = "Greater_1";
  id_to_name_data[80] = "Sort_3";
  id_to_name_data[238] = "Lt_2";
  id_to_name_data[243] = "Node_2";
  id_to_name_data[152] = "Ord.constructor_0";
  id_to_name_data[56] = "Fst_split_a_1";
  id_to_name_data[16] = "MapInl_5";
  id_to_name_data[10] = "X5Bx5Dx221Ex2Drefl_0";
  id_to_name_data[176] = "Monus_split_3";
  id_to_name_data[293] = "Refl";
  id_to_name_data[46] = "X5Bx5Dx221Ex2Dtrans_1";
  id_to_name_data[65] = "MapMaybe_4";
  id_to_name_data[206] = "X2Dx221Ex2Dx2264_0";
  id_to_name_data[222] = "X2Dx221Ex2Dx2264";
  id_to_name_data[249] = "SEQ";
  id_to_name_data[31] = "If_3";
  id_to_name_data[58] = "X2264x2Ddec_3";
  id_to_name_data[87] = "X5Bx5Dx2Dx2264x2DI_4";
  id_to_name_data[3] = "Subst_6";
  id_to_name_data[219] = "Right";
  id_to_name_data[29] = "MapInl_2";
  id_to_name_data[109] = "TDO.constructor";
  id_to_name_data[110] = "TriNat_1";
  id_to_name_data[138] = "Left_3";
  id_to_name_data[35] = "Right_4";
  id_to_name_data[189] = "MapInr_0";
  id_to_name_data[145] = "Less_1";
  id_to_name_data[100] = "Tt_0";
  id_to_name_data[223] = "X5Bx5Dx221Ex2Dtrans_split_c_11";
  id_to_name_data[115] = "MapInl_0";
  id_to_name_data[41] = "X2264x2Dsuc_3";
  id_to_name_data[160] = "Z_x2Bx2B__0";
  id_to_name_data[147] = "Insert_5";
  id_to_name_data[277] = "Left";
  id_to_name_data[282] = "Z_x2Bx2B__2";
  id_to_name_data[287] = "Lookup_4";
  id_to_name_data[48] = "Leaf_1";
  id_to_name_data[83] = "Main_0";
  id_to_name_data[27] = "X2Dx221Ex2Dx2264x2DI_2";
  id_to_name_data[184] = "Node";
  id_to_name_data[34] = "Right_0";
  id_to_name_data[177] = "X5Bx5Dx221Ex2Drefl_1";
;

  // Builds main term
  mem.size = 0;
  mem.node = (u64*)malloc(HEAP_SIZE);
  assert(mem.node);
  if (argc <= 1) {
    mem.node[mem.size++] = Cal(0, _MAIN_, 0);
  } else {
    mem.node[mem.size++] = Cal(argc - 1, _MAIN_, 1);
    for (u64 i = 1; i < argc; ++i) {
      mem.node[mem.size++] = parse_arg(argv[i], id_to_name_data, id_to_name_size);
    }
  }

  // Reduces and benchmarks
  //printf("Reducing.\n");
  gettimeofday(&start, NULL);
  ffi_normal((u8*)mem.node, mem.size, 0);
  gettimeofday(&stop, NULL);

  // Prints result statistics
  u64 delta_time = (stop.tv_sec - start.tv_sec) * 1000000 + stop.tv_usec - start.tv_usec;
  double rwt_per_sec = (double)ffi_cost / (double)delta_time;
  fprintf(stderr, "Rewrites: %"PRIu64" (%.2f MR/s).\n", ffi_cost, rwt_per_sec);
  fprintf(stderr, "Mem.Size: %"PRIu64" words.\n", ffi_size);
  fprintf(stderr, "\n");

  // Prints result normal form
  const u64 code_mcap = 256 * 256 * 256; // max code size = 16 MB
  char* code_data = (char*)malloc(code_mcap * sizeof(char));
  assert(code_data);
  readback(code_data, code_mcap, &mem, mem.node[0], id_to_name_data, id_to_name_size);
  printf("%s\n", code_data);

  // Cleanup
  free(code_data);
  free(mem.node);
}
