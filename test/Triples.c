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
#define _TRIPLE__3_ (29)
#define _EQ__2_ (54)
#define _GO__3_ (34)
#define _RANGE__0_ (32)
#define _MAIN__0_ (21)
#define _FILTER__2_ (65)
#define _ALLTRIPLES__0_ (70)
#define _EQ__SPLIT__1_ (55)
#define _FILTER__1_ (69)
#define _TRD__SPLIT__A__1_ (64)
#define _GO__SPLIT__C__4_ (72)
#define _CARTESIAN__0_ (33)
#define _TEST1__0_ (22)
#define _TRD__0_ (43)
#define _FILTER__3_ (7)
#define _MONUS__SPLIT__3_ (41)
#define _APPEND__0_ (52)
#define _BIND__4_ (6)
#define _TRIPLES__1_ (23)
#define _SUMALL__SPLIT__A__1_ (24)
#define _CONS__2_ (15)
#define _TRD__1_ (44)
#define _BIND__0_ (49)
#define _FST__SPLIT__A__1_ (31)
#define _APPEND__1_ (57)
#define _BIND__3_ (67)
#define _IF__THEN__ELSE____0_ (61)
#define _IF__THEN__ELSE____1_ (71)
#define _CARTESIAN__SPLIT__A__1_ (11)
#define _FILTER__0_ (45)
#define _IF__THEN__ELSE____3_ (35)
#define _SND__0_ (47)
#define _RANGE__1_ (18)
#define _APPEND__2_ (51)
#define _FILTER__SPLIT__C__3_ (8)
#define _ALLTRIPLES__1_ (56)
#define _GO__2_ (9)
#define _SND__1_ (37)
#define _IF__THEN__ELSE____4_ (36)
#define _IF__THEN__ELSE____SPLIT__B__4_ (39)
#define _SUMALL__1_ (4)
#define _FST__1_ (26)
#define _GO__E__4_ (46)
#define _GO__1_ (0)
#define _GO__4_ (1)
#define _TRIPLE__1_ (28)
#define _TRIPLE__2_ (30)
#define _BIND__1_ (5)
#define _CARTESIAN__1_ (10)
#define _SND__SPLIT__A__1_ (38)
#define _CONS__0_ (66)
#define _MAIN_ (73)
#define _CONS__1_ (42)
#define _APPEND__3_ (16)
#define _FST__0_ (25)
#define _BIND__SPLIT__C__4_ (53)
#define _SUMALL__SPLIT__B__3_ (2)
#define _SUMALL__0_ (48)
#define _PUTSTRLN__1_ (27)
#define _TRIPLE__0_ (50)
#define _RANGE__2_ (19)
#define _GO__0_ (68)
#define _BIND__2_ (58)
#define _MONUS__2_ (62)
#define _APPEND__SPLIT__B__3_ (12)
#define _TRIPLES__0_ (40)
#define _IF__THEN__ELSE____2_ (63)
#define _NIL__0_ (20)

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
            case _TRIPLE__3_: {
              if (get_ari(term) == 3) {
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
            case _GO__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _RANGE__0_: {
              if (get_ari(term) == 0) {
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
            case _FILTER__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _ALLTRIPLES__0_: {
              if (get_ari(term) == 0) {
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
            case _FILTER__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TRD__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _GO__SPLIT__C__4_: {
              if (get_ari(term) == 4) {
                stk_push(&stack, host);
                host = get_loc(term, 2);
                continue;
              }
            };
            case _CARTESIAN__0_: {
              if (get_ari(term) == 0) {
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
            case _TRD__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FILTER__3_: {
              if (get_ari(term) == 3) {
                init = 0;
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
            case _APPEND__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _BIND__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _TRIPLES__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _SUMALL__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _CONS__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _TRD__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _BIND__0_: {
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
            case _APPEND__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _BIND__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _IF__THEN__ELSE____0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _IF__THEN__ELSE____1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _CARTESIAN__SPLIT__A__1_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _FILTER__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _IF__THEN__ELSE____3_: {
              if (get_ari(term) == 3) {
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
            case _RANGE__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _APPEND__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _FILTER__SPLIT__C__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 2);
                continue;
              }
            };
            case _ALLTRIPLES__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _GO__2_: {
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
            case _IF__THEN__ELSE____4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _IF__THEN__ELSE____SPLIT__B__4_: {
              if (get_ari(term) == 4) {
                stk_push(&stack, host);
                host = get_loc(term, 1);
                continue;
              }
            };
            case _SUMALL__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _FST__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _GO__E__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _GO__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _GO__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _TRIPLE__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TRIPLE__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _BIND__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _CARTESIAN__1_: {
              if (get_ari(term) == 1) {
                init = 0;
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
            case _CONS__0_: {
              if (get_ari(term) == 0) {
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
            case _CONS__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _APPEND__3_: {
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
            case _BIND__SPLIT__C__4_: {
              if (get_ari(term) == 4) {
                stk_push(&stack, host);
                host = get_loc(term, 2);
                continue;
              }
            };
            case _SUMALL__SPLIT__B__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 1);
                continue;
              }
            };
            case _SUMALL__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _PUTSTRLN__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TRIPLE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _RANGE__2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _GO__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _BIND__2_: {
              if (get_ari(term) == 2) {
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
            case _APPEND__SPLIT__B__3_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 1);
                continue;
              }
            };
            case _TRIPLES__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _IF__THEN__ELSE____2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _NIL__0_: {
              if (get_ari(term) == 0) {
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
            case _TRIPLE__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                u64 done = Ctr(3, 3, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
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
                u64 done = Cal(1, 55, cal_2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _GO__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 1, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _RANGE__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 19, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAIN__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 22, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FILTER__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 7, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _ALLTRIPLES__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 56, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
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
                u64 done = Ctr(0, 60, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 59, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _FILTER__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 7, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TRD__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 3u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 0), 2);
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
                u64 done = dp1_2;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _GO__SPLIT__C__4_: {
              if (get_tag(ask_arg(mem,term,2)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 2), 2);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == U32 && get_val(ask_arg(mem, term, 2)) == 0u)) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 20, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 3));
                init = 1;
                continue;
              }
              if (1) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, term, 3);
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
                u64 cal_10 = alloc(mem, 4);
                link(mem, cal_10 + 0, ask_arg(mem, term, 0));
                link(mem, cal_10 + 1, ask_arg(mem, term, 1));
                link(mem, cal_10 + 2, ask_arg(mem, term, 2));
                link(mem, cal_10 + 3, dp1_2);
                u64 ctr_11 = alloc(mem, 0);
                u64 ctr_12 = alloc(mem, 0);
                u64 ret_13;
                if (get_tag(U_32(1)) == U32 && get_tag(dp1_7) == U32) {
                  ret_13 = U_32(get_val(U_32(1)) + get_val(dp1_7));
                  inc_cost(mem);
                } else {
                  u64 op2_14 = alloc(mem, 2);
                  link(mem, op2_14 + 0, U_32(1));
                  link(mem, op2_14 + 1, dp1_7);
                  ret_13 = Op2(ADD, op2_14);
                }
                u64 cal_15 = alloc(mem, 4);
                link(mem, cal_15 + 0, Ctr(0, 17, ctr_11));
                link(mem, cal_15 + 1, Ctr(0, 17, ctr_12));
                link(mem, cal_15 + 2, Cal(4, 46, cal_10));
                link(mem, cal_15 + 3, ret_13);
                u64 cal_16 = alloc(mem, 2);
                link(mem, cal_16 + 0, dp0_6);
                link(mem, cal_16 + 1, Cal(4, 1, cal_15));
                u64 done = Cal(2, 15, cal_16);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _CARTESIAN__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 10, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TEST1__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, U_32(10));
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Cal(1, 23, cal_0));
                u64 done = Cal(1, 4, cal_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TRD__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 44, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FILTER__3_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 done = Cal(3, 8, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
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
            case _APPEND__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 16, cal_3));
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
            case _BIND__4_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 4);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                u64 done = Cal(4, 53, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _TRIPLES__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 1);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Ctr(0, 17, ctr_0));
                link(mem, cal_3 + 1, Cal(0, 33, cal_1));
                link(mem, cal_3 + 2, Cal(1, 56, cal_2));
                u64 done = Cal(3, 7, cal_3);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _SUMALL__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 13u)) {
                inc_cost(mem);
                u64 done = U_32(0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 14u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 0), 1);
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
                u64 cpy_5 = ask_arg(mem, ask_arg(mem, term, 0), 0);
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
                u64 ctr_10 = alloc(mem, 2);
                link(mem, ctr_10 + 0, dp0_6);
                link(mem, ctr_10 + 1, dp0_1);
                u64 cal_11 = alloc(mem, 3);
                link(mem, cal_11 + 0, Ctr(2, 14, ctr_10));
                link(mem, cal_11 + 1, dp1_7);
                link(mem, cal_11 + 2, dp1_2);
                u64 done = Cal(3, 2, cal_11);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _CONS__2_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 2);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                u64 done = Ctr(2, 14, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _TRD__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 64, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _BIND__0_: {
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
                link(mem, lam_3 + 1, Cal(4, 6, cal_4));
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
            case _FST__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 3u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 0), 0);
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
                u64 done = dp1_2;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _APPEND__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 16, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _BIND__3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 6, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _IF__THEN__ELSE____0_: {
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
                link(mem, lam_3 + 1, Cal(4, 36, cal_4));
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
            case _IF__THEN__ELSE____1_: {
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
                link(mem, lam_2 + 1, Cal(4, 36, cal_3));
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
            case _CARTESIAN__SPLIT__A__1_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 3u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 0), 2);
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
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 0), 1);
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
                u64 cpy_20 = ask_arg(mem, ask_arg(mem, term, 0), 0);
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
                u64 ret_32;
                if (get_tag(dp0_26) == U32 && get_tag(dp1_27) == U32) {
                  ret_32 = U_32(get_val(dp0_26) * get_val(dp1_27));
                  inc_cost(mem);
                } else {
                  u64 op2_33 = alloc(mem, 2);
                  link(mem, op2_33 + 0, dp0_26);
                  link(mem, op2_33 + 1, dp1_27);
                  ret_32 = Op2(MUL, op2_33);
                }
                u64 ret_34;
                if (get_tag(dp0_16) == U32 && get_tag(dp1_17) == U32) {
                  ret_34 = U_32(get_val(dp0_16) * get_val(dp1_17));
                  inc_cost(mem);
                } else {
                  u64 op2_35 = alloc(mem, 2);
                  link(mem, op2_35 + 0, dp0_16);
                  link(mem, op2_35 + 1, dp1_17);
                  ret_34 = Op2(MUL, op2_35);
                }
                u64 ret_30;
                if (get_tag(ret_32) == U32 && get_tag(ret_34) == U32) {
                  ret_30 = U_32(get_val(ret_32) + get_val(ret_34));
                  inc_cost(mem);
                } else {
                  u64 op2_31 = alloc(mem, 2);
                  link(mem, op2_31 + 0, ret_32);
                  link(mem, op2_31 + 1, ret_34);
                  ret_30 = Op2(ADD, op2_31);
                }
                u64 ret_36;
                if (get_tag(dp0_6) == U32 && get_tag(dp1_7) == U32) {
                  ret_36 = U_32(get_val(dp0_6) * get_val(dp1_7));
                  inc_cost(mem);
                } else {
                  u64 op2_37 = alloc(mem, 2);
                  link(mem, op2_37 + 0, dp0_6);
                  link(mem, op2_37 + 1, dp1_7);
                  ret_36 = Op2(MUL, op2_37);
                }
                u64 cal_38 = alloc(mem, 2);
                link(mem, cal_38 + 0, ret_30);
                link(mem, cal_38 + 1, ret_36);
                u64 done = Cal(2, 54, cal_38);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _FILTER__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 7, cal_3));
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
            case _IF__THEN__ELSE____3_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 4);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, ask_arg(mem, term, 2));
                link(mem, cal_1 + 3, Var(lam_0));
                link(mem, lam_0 + 1, Cal(4, 36, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
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
                link(mem, lam_0 + 1, Cal(1, 37, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _RANGE__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 19, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _APPEND__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 16, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _FILTER__SPLIT__C__3_: {
              if (get_tag(ask_arg(mem,term,2)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 2), 2);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 13u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 13, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 14u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 2), 1);
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
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 2), 0);
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
                u64 cpy_20 = ask_arg(mem, term, 1);
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
                u64 ctr_30 = alloc(mem, 0);
                u64 app_31 = alloc(mem, 2);
                link(mem, app_31 + 0, dp1_22);
                link(mem, app_31 + 1, dp0_16);
                u64 ctr_32 = alloc(mem, 0);
                u64 cal_33 = alloc(mem, 3);
                link(mem, cal_33 + 0, Ctr(0, 17, ctr_32));
                link(mem, cal_33 + 1, dp0_26);
                link(mem, cal_33 + 2, dp0_6);
                u64 cal_34 = alloc(mem, 2);
                link(mem, cal_34 + 0, dp1_17);
                link(mem, cal_34 + 1, Cal(3, 7, cal_33));
                u64 ctr_35 = alloc(mem, 0);
                u64 cal_36 = alloc(mem, 3);
                link(mem, cal_36 + 0, Ctr(0, 17, ctr_35));
                link(mem, cal_36 + 1, dp1_27);
                link(mem, cal_36 + 2, dp1_7);
                u64 cal_37 = alloc(mem, 4);
                link(mem, cal_37 + 0, Ctr(0, 17, ctr_30));
                link(mem, cal_37 + 1, App(app_31));
                link(mem, cal_37 + 2, Cal(2, 15, cal_34));
                link(mem, cal_37 + 3, Cal(3, 7, cal_36));
                u64 done = Cal(4, 36, cal_37);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              break;
            };
            case _ALLTRIPLES__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 ctr_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, U_32(1));
                link(mem, cal_2 + 1, ask_arg(mem, term, 0));
                u64 lam_3 = alloc(mem, 2);
                u64 cpy_4 = Var(lam_3);
                u64 dp0_5;
                u64 dp1_6;
                if (get_tag(cpy_4) == U32) {
                  inc_cost(mem);
                  dp0_5 = cpy_4;
                  dp1_6 = cpy_4;
                } else {
                  u64 dup_7 = alloc(mem, 3);
                  u64 col_8 = gen_dupk(mem);
                  link(mem, dup_7 + 2, cpy_4);
                  dp0_5 = Dp0(col_8, dup_7);
                  dp1_6 = Dp1(col_8, dup_7);
                }
                u64 ctr_9 = alloc(mem, 0);
                u64 ctr_10 = alloc(mem, 0);
                u64 cal_11 = alloc(mem, 2);
                link(mem, cal_11 + 0, U_32(1));
                link(mem, cal_11 + 1, dp0_5);
                u64 lam_12 = alloc(mem, 2);
                u64 cpy_13 = Var(lam_12);
                u64 dp0_14;
                u64 dp1_15;
                if (get_tag(cpy_13) == U32) {
                  inc_cost(mem);
                  dp0_14 = cpy_13;
                  dp1_15 = cpy_13;
                } else {
                  u64 dup_16 = alloc(mem, 3);
                  u64 col_17 = gen_dupk(mem);
                  link(mem, dup_16 + 2, cpy_13);
                  dp0_14 = Dp0(col_17, dup_16);
                  dp1_15 = Dp1(col_17, dup_16);
                }
                u64 ctr_18 = alloc(mem, 0);
                u64 ctr_19 = alloc(mem, 0);
                u64 cal_20 = alloc(mem, 2);
                link(mem, cal_20 + 0, U_32(1));
                link(mem, cal_20 + 1, dp0_14);
                u64 lam_21 = alloc(mem, 2);
                u64 cal_22 = alloc(mem, 3);
                link(mem, cal_22 + 0, Var(lam_21));
                link(mem, cal_22 + 1, dp1_15);
                link(mem, cal_22 + 2, dp1_6);
                u64 cal_23 = alloc(mem, 0);
                u64 cal_24 = alloc(mem, 2);
                link(mem, cal_24 + 0, Cal(3, 29, cal_22));
                link(mem, cal_24 + 1, Cal(0, 20, cal_23));
                link(mem, lam_21 + 1, Cal(2, 15, cal_24));
                u64 cal_25 = alloc(mem, 4);
                link(mem, cal_25 + 0, Ctr(0, 17, ctr_18));
                link(mem, cal_25 + 1, Ctr(0, 17, ctr_19));
                link(mem, cal_25 + 2, Cal(2, 19, cal_20));
                link(mem, cal_25 + 3, Lam(lam_21));
                link(mem, lam_12 + 1, Cal(4, 6, cal_25));
                u64 cal_26 = alloc(mem, 4);
                link(mem, cal_26 + 0, Ctr(0, 17, ctr_9));
                link(mem, cal_26 + 1, Ctr(0, 17, ctr_10));
                link(mem, cal_26 + 2, Cal(2, 19, cal_11));
                link(mem, cal_26 + 3, Lam(lam_12));
                link(mem, lam_3 + 1, Cal(4, 6, cal_26));
                u64 cal_27 = alloc(mem, 4);
                link(mem, cal_27 + 0, Ctr(0, 17, ctr_0));
                link(mem, cal_27 + 1, Ctr(0, 17, ctr_1));
                link(mem, cal_27 + 2, Cal(2, 19, cal_2));
                link(mem, cal_27 + 3, Lam(lam_3));
                u64 done = Cal(4, 6, cal_27);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _GO__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 1, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
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
                u64 done = Cal(1, 38, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _IF__THEN__ELSE____4_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 4);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                u64 done = Cal(4, 39, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _IF__THEN__ELSE____SPLIT__B__4_: {
              if (get_tag(ask_arg(mem,term,1)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 1), 1);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 59u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 3);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                clear(mem, get_loc(ask_arg(mem, term, 1), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 60u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                clear(mem, get_loc(ask_arg(mem, term, 1), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 3));
                init = 1;
                continue;
              }
              break;
            };
            case _SUMALL__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 24, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
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
                u64 done = Cal(1, 31, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _GO__E__4_: {
              if (1) {
                inc_cost(mem);
                u64 ret_0;
                if (get_tag(ask_arg(mem, term, 2)) == U32 && get_tag(U_32(1)) == U32) {
                  ret_0 = U_32(get_val(ask_arg(mem, term, 2)) - get_val(U_32(1)));
                  inc_cost(mem);
                } else {
                  u64 op2_1 = alloc(mem, 2);
                  link(mem, op2_1 + 0, ask_arg(mem, term, 2));
                  link(mem, op2_1 + 1, U_32(1));
                  ret_0 = Op2(SUB, op2_1);
                }
                u64 done = ret_0;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 3));
                init = 1;
                continue;
              }
              break;
            };
            case _GO__1_: {
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
                link(mem, lam_2 + 1, Cal(4, 1, cal_3));
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
            case _GO__4_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 4);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                u64 done = Cal(4, 72, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _TRIPLE__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 3);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, Var(lam_0));
                link(mem, cal_2 + 2, Var(lam_1));
                link(mem, lam_1 + 1, Cal(3, 29, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TRIPLE__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 3);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, ask_arg(mem, term, 1));
                link(mem, cal_1 + 2, Var(lam_0));
                link(mem, lam_0 + 1, Cal(3, 29, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _BIND__1_: {
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
                link(mem, lam_2 + 1, Cal(4, 6, cal_3));
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
            case _CARTESIAN__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 11, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
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
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 3u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 0), 1);
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
                u64 done = dp1_2;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _CONS__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 15, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAIN_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 21, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _CONS__1_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 2);
                link(mem, cal_1 + 0, ask_arg(mem, term, 0));
                link(mem, cal_1 + 1, Var(lam_0));
                link(mem, lam_0 + 1, Cal(2, 15, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _APPEND__3_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 done = Cal(3, 12, cal_0);
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
                link(mem, lam_0 + 1, Cal(1, 26, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _BIND__SPLIT__C__4_: {
              if (get_tag(ask_arg(mem,term,2)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 2), 2);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 13u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 13, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 3));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 14u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 2), 1);
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
                u64 cpy_5 = ask_arg(mem, ask_arg(mem, term, 2), 0);
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
                u64 cpy_10 = ask_arg(mem, term, 3);
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
                u64 ctr_15 = alloc(mem, 0);
                u64 app_16 = alloc(mem, 2);
                link(mem, app_16 + 0, dp0_11);
                link(mem, app_16 + 1, dp1_7);
                u64 ctr_17 = alloc(mem, 0);
                u64 ctr_18 = alloc(mem, 0);
                u64 cal_19 = alloc(mem, 4);
                link(mem, cal_19 + 0, Ctr(0, 17, ctr_17));
                link(mem, cal_19 + 1, Ctr(0, 17, ctr_18));
                link(mem, cal_19 + 2, dp1_2);
                link(mem, cal_19 + 3, dp1_12);
                u64 cal_20 = alloc(mem, 3);
                link(mem, cal_20 + 0, Ctr(0, 17, ctr_15));
                link(mem, cal_20 + 1, App(app_16));
                link(mem, cal_20 + 2, Cal(4, 6, cal_19));
                u64 done = Cal(3, 16, cal_20);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _SUMALL__SPLIT__B__3_: {
              if (get_tag(ask_arg(mem,term,1)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 1), 1);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 3u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 1), 2);
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
                u64 cpy_5 = ask_arg(mem, ask_arg(mem, term, 1), 1);
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
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 1), 0);
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
                u64 cal_21 = alloc(mem, 1);
                link(mem, cal_21 + 0, ask_arg(mem, term, 2));
                u64 ret_19;
                if (get_tag(Cal(1, 4, cal_21)) == U32 && get_tag(dp1_12) == U32) {
                  ret_19 = U_32(get_val(Cal(1, 4, cal_21)) + get_val(dp1_12));
                  inc_cost(mem);
                } else {
                  u64 op2_20 = alloc(mem, 2);
                  link(mem, op2_20 + 0, Cal(1, 4, cal_21));
                  link(mem, op2_20 + 1, dp1_12);
                  ret_19 = Op2(ADD, op2_20);
                }
                u64 ret_17;
                if (get_tag(ret_19) == U32 && get_tag(dp1_7) == U32) {
                  ret_17 = U_32(get_val(ret_19) + get_val(dp1_7));
                  inc_cost(mem);
                } else {
                  u64 op2_18 = alloc(mem, 2);
                  link(mem, op2_18 + 0, ret_19);
                  link(mem, op2_18 + 1, dp1_7);
                  ret_17 = Op2(ADD, op2_18);
                }
                u64 ret_15;
                if (get_tag(ret_17) == U32 && get_tag(dp1_2) == U32) {
                  ret_15 = U_32(get_val(ret_17) + get_val(dp1_2));
                  inc_cost(mem);
                } else {
                  u64 op2_16 = alloc(mem, 2);
                  link(mem, op2_16 + 0, ret_17);
                  link(mem, op2_16 + 1, dp1_2);
                  ret_15 = Op2(ADD, op2_16);
                }
                u64 done = ret_15;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 1), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              break;
            };
            case _SUMALL__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 4, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _PUTSTRLN__1_: {
              if (1) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TRIPLE__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 29, cal_3));
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
            case _RANGE__2_: {
              if (1) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, term, 0);
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
                u64 ret_7;
                if (get_tag(U_32(1)) == U32 && get_tag(ask_arg(mem, term, 1)) == U32) {
                  ret_7 = U_32(get_val(U_32(1)) + get_val(ask_arg(mem, term, 1)));
                  inc_cost(mem);
                } else {
                  u64 op2_8 = alloc(mem, 2);
                  link(mem, op2_8 + 0, U_32(1));
                  link(mem, op2_8 + 1, ask_arg(mem, term, 1));
                  ret_7 = Op2(ADD, op2_8);
                }
                u64 cal_9 = alloc(mem, 2);
                link(mem, cal_9 + 0, ret_7);
                link(mem, cal_9 + 1, dp0_1);
                u64 cal_10 = alloc(mem, 4);
                link(mem, cal_10 + 0, Ctr(0, 17, ctr_5));
                link(mem, cal_10 + 1, Ctr(0, 17, ctr_6));
                link(mem, cal_10 + 2, Cal(2, 62, cal_9));
                link(mem, cal_10 + 3, dp1_2);
                u64 done = Cal(4, 1, cal_10);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _GO__0_: {
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
                link(mem, lam_3 + 1, Cal(4, 1, cal_4));
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
            case _BIND__2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 6, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
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
                u64 done = Cal(3, 41, cal_12);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _APPEND__SPLIT__B__3_: {
              if (get_tag(ask_arg(mem,term,1)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 1), 1);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 13u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 1), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 14u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 1), 1);
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
                u64 cpy_5 = ask_arg(mem, ask_arg(mem, term, 1), 0);
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
                u64 ctr_10 = alloc(mem, 0);
                u64 cal_11 = alloc(mem, 3);
                link(mem, cal_11 + 0, Ctr(0, 17, ctr_10));
                link(mem, cal_11 + 1, dp1_2);
                link(mem, cal_11 + 2, ask_arg(mem, term, 2));
                u64 cal_12 = alloc(mem, 2);
                link(mem, cal_12 + 0, dp1_7);
                link(mem, cal_12 + 1, Cal(3, 16, cal_11));
                u64 done = Cal(2, 15, cal_12);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 1), 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                init = 1;
                continue;
              }
              break;
            };
            case _TRIPLES__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 23, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _IF__THEN__ELSE____2_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 4);
                link(mem, cal_2 + 0, ask_arg(mem, term, 0));
                link(mem, cal_2 + 1, ask_arg(mem, term, 1));
                link(mem, cal_2 + 2, Var(lam_0));
                link(mem, cal_2 + 3, Var(lam_1));
                link(mem, lam_1 + 1, Cal(4, 36, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _NIL__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 13, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
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
  const u64 id_to_name_size = 74;
  char* id_to_name_data[id_to_name_size];
  id_to_name_data[16] = "Append_3";
  id_to_name_data[37] = "Snd_1";
  id_to_name_data[57] = "Append_1";
  id_to_name_data[19] = "Range_2";
  id_to_name_data[5] = "Bind_1";
  id_to_name_data[15] = "Cons_2";
  id_to_name_data[35] = "If_then_else__3";
  id_to_name_data[40] = "Triples_0";
  id_to_name_data[55] = "Eq_split_1";
  id_to_name_data[26] = "Fst_1";
  id_to_name_data[24] = "Sumall_split_a_1";
  id_to_name_data[45] = "Filter_0";
  id_to_name_data[47] = "Snd_0";
  id_to_name_data[52] = "Append_0";
  id_to_name_data[38] = "Snd_split_a_1";
  id_to_name_data[64] = "Trd_split_a_1";
  id_to_name_data[70] = "Alltriples_0";
  id_to_name_data[23] = "Triples_1";
  id_to_name_data[69] = "Filter_1";
  id_to_name_data[59] = "False";
  id_to_name_data[7] = "Filter_3";
  id_to_name_data[9] = "Go_2";
  id_to_name_data[27] = "PutStrLn_1";
  id_to_name_data[50] = "Triple_0";
  id_to_name_data[22] = "Test1_0";
  id_to_name_data[3] = "Triple";
  id_to_name_data[61] = "If_then_else__0";
  id_to_name_data[63] = "If_then_else__2";
  id_to_name_data[0] = "Go_1";
  id_to_name_data[13] = "Nil";
  id_to_name_data[51] = "Append_2";
  id_to_name_data[2] = "Sumall_split_b_3";
  id_to_name_data[62] = "Monus_2";
  id_to_name_data[66] = "Cons_0";
  id_to_name_data[68] = "Go_0";
  id_to_name_data[34] = "Go_3";
  id_to_name_data[11] = "Cartesian_split_a_1";
  id_to_name_data[42] = "Cons_1";
  id_to_name_data[29] = "Triple_3";
  id_to_name_data[58] = "Bind_2";
  id_to_name_data[72] = "Go_split_c_4";
  id_to_name_data[14] = "Cons";
  id_to_name_data[17] = "Matteo";
  id_to_name_data[30] = "Triple_2";
  id_to_name_data[31] = "Fst_split_a_1";
  id_to_name_data[32] = "Range_0";
  id_to_name_data[65] = "Filter_2";
  id_to_name_data[54] = "Eq_2";
  id_to_name_data[41] = "Monus_split_3";
  id_to_name_data[33] = "Cartesian_0";
  id_to_name_data[12] = "Append_split_b_3";
  id_to_name_data[21] = "Main_0";
  id_to_name_data[6] = "Bind_4";
  id_to_name_data[28] = "Triple_1";
  id_to_name_data[39] = "If_then_else__split_b_4";
  id_to_name_data[20] = "Nil_0";
  id_to_name_data[25] = "Fst_0";
  id_to_name_data[43] = "Trd_0";
  id_to_name_data[10] = "Cartesian_1";
  id_to_name_data[18] = "Range_1";
  id_to_name_data[46] = "Go_e_4";
  id_to_name_data[53] = "Bind_split_c_4";
  id_to_name_data[36] = "If_then_else__4";
  id_to_name_data[56] = "Alltriples_1";
  id_to_name_data[1] = "Go_4";
  id_to_name_data[44] = "Trd_1";
  id_to_name_data[48] = "Sumall_0";
  id_to_name_data[60] = "True";
  id_to_name_data[4] = "Sumall_1";
  id_to_name_data[67] = "Bind_3";
  id_to_name_data[71] = "If_then_else__1";
  id_to_name_data[73] = "Main";
  id_to_name_data[8] = "Filter_split_c_3";
  id_to_name_data[49] = "Bind_0";
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
