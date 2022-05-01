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
#define _SUC__1_ (60)
#define _TEST3__0_ (45)
#define _ITE__4_ (19)
#define _TAIL__SPLIT__C_ (48)
#define _TWO__0_ (52)
#define _FOE__0_ (10)
#define _MAP__0_ (21)
#define _TAIL__0_ (46)
#define _NIL__0_ (26)
#define _Z__X2B____2_ (28)
#define _FIE__0_ (7)
#define _LOOP__0_ (42)
#define _PRED__SPLIT__A_ (11)
#define _CON__3_ (51)
#define _FIE__1_ (37)
#define _ID__1_ (54)
#define _MAIN__0_ (62)
#define _Z__X2B____0_ (6)
#define _NOT__0_ (36)
#define _NOT__SPLIT__A_ (34)
#define _TWICE__SPLIT__A_ (17)
#define _CONSUME__SPLIT__A_ (30)
#define _TEST4__0_ (43)
#define _PRED__1_ (1)
#define _HEAD__0_ (31)
#define _POW2__0_ (13)
#define _MAP__5_ (22)
#define _HEAD__3_ (32)
#define _IF_ (64)
#define _TAIL__3_ (47)
#define _Z123X27X23X7CHX5CX65LLO__0_ (44)
#define _POW2__SPLIT__A_ (23)
#define _CONSUME__0_ (2)
#define _POW2__1_ (61)
#define _PRED__0_ (0)
#define _FUN__0_ (5)
#define _MAIN_ (63)
#define _FOE__1_ (50)
#define _ITE__SPLIT__B_ (35)
#define _CON__0_ (40)
#define _CONSUME__1_ (3)
#define _ITE__0_ (18)
#define _ZERO__0_ (9)
#define _SUC__0_ (8)
#define _TWICE__0_ (14)
#define _THREE__0_ (15)
#define _ID__0_ (53)
#define _MATCH_ (4)
#define _TWICE__1_ (16)
#define _NOT__1_ (33)
#define _TEST1__0_ (59)
#define _HEAD__SPLIT__C_ (49)
#define _Z__X2B____SPLIT__A_ (29)
#define _TRUE__0_ (58)
#define _FALSE__0_ (56)
#define _ONE__0_ (20)
#define _MAP__SPLIT__E_ (38)
#define _TEST2__0_ (12)

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
            case _SUC__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _TEST3__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _ITE__4_: {
              if (get_ari(term) == 4) {
                init = 0;
                continue;
              }
            };
            case _TAIL__SPLIT__C_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 2);
                continue;
              }
            };
            case _TWO__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FOE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAP__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _TAIL__0_: {
              if (get_ari(term) == 0) {
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
            case _Z__X2B____2_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _FIE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _LOOP__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _PRED__SPLIT__A_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _CON__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _FIE__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _ID__1_: {
              if (get_ari(term) == 1) {
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
            case _Z__X2B____0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _NOT__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _NOT__SPLIT__A_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _TWICE__SPLIT__A_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _CONSUME__SPLIT__A_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _TEST4__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _PRED__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _HEAD__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _POW2__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAP__5_: {
              if (get_ari(term) == 5) {
                init = 0;
                continue;
              }
            };
            case _HEAD__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _IF_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _TAIL__3_: {
              if (get_ari(term) == 3) {
                init = 0;
                continue;
              }
            };
            case _Z123X27X23X7CHX5CX65LLO__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _POW2__SPLIT__A_: {
              if (get_ari(term) == 1) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _CONSUME__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _POW2__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _PRED__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _FUN__0_: {
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
            case _FOE__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _ITE__SPLIT__B_: {
              if (get_ari(term) == 4) {
                stk_push(&stack, host);
                host = get_loc(term, 1);
                continue;
              }
            };
            case _CON__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _CONSUME__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _ITE__0_: {
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
            case _SUC__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _TWICE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _THREE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _ID__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MATCH_: {
              if (get_ari(term) == 2) {
                init = 0;
                continue;
              }
            };
            case _TWICE__1_: {
              if (get_ari(term) == 1) {
                init = 0;
                continue;
              }
            };
            case _NOT__1_: {
              if (get_ari(term) == 1) {
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
            case _HEAD__SPLIT__C_: {
              if (get_ari(term) == 3) {
                stk_push(&stack, host);
                host = get_loc(term, 2);
                continue;
              }
            };
            case _Z__X2B____SPLIT__A_: {
              if (get_ari(term) == 2) {
                stk_push(&stack, host);
                host = get_loc(term, 0);
                continue;
              }
            };
            case _TRUE__0_: {
              if (get_ari(term) == 0) {
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
            case _ONE__0_: {
              if (get_ari(term) == 0) {
                init = 0;
                continue;
              }
            };
            case _MAP__SPLIT__E_: {
              if (get_ari(term) == 5) {
                stk_push(&stack, host);
                host = get_loc(term, 4);
                continue;
              }
            };
            case _TEST2__0_: {
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
            case _SUC__1_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 1);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                u64 done = Ctr(1, 25, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TEST3__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_3 = alloc(mem, 0);
                u64 ctr_4 = alloc(mem, 0);
                u64 app_2 = alloc(mem, 2);
                link(mem, app_2 + 0, Cal(0, 31, cal_3));
                link(mem, app_2 + 1, Ctr(0, 41, ctr_4));
                u64 ctr_5 = alloc(mem, 0);
                u64 app_1 = alloc(mem, 2);
                link(mem, app_1 + 0, App(app_2));
                link(mem, app_1 + 1, Ctr(0, 41, ctr_5));
                u64 cal_9 = alloc(mem, 0);
                u64 ctr_10 = alloc(mem, 0);
                u64 app_8 = alloc(mem, 2);
                link(mem, app_8 + 0, Cal(0, 46, cal_9));
                link(mem, app_8 + 1, Ctr(0, 41, ctr_10));
                u64 ctr_11 = alloc(mem, 0);
                u64 app_7 = alloc(mem, 2);
                link(mem, app_7 + 0, App(app_8));
                link(mem, app_7 + 1, Ctr(0, 41, ctr_11));
                u64 cal_17 = alloc(mem, 0);
                u64 ctr_18 = alloc(mem, 0);
                u64 app_16 = alloc(mem, 2);
                link(mem, app_16 + 0, Cal(0, 21, cal_17));
                link(mem, app_16 + 1, Ctr(0, 41, ctr_18));
                u64 ctr_19 = alloc(mem, 0);
                u64 app_15 = alloc(mem, 2);
                link(mem, app_15 + 0, App(app_16));
                link(mem, app_15 + 1, Ctr(0, 41, ctr_19));
                u64 ctr_20 = alloc(mem, 0);
                u64 app_14 = alloc(mem, 2);
                link(mem, app_14 + 0, App(app_15));
                link(mem, app_14 + 1, Ctr(0, 41, ctr_20));
                u64 cal_21 = alloc(mem, 0);
                u64 app_13 = alloc(mem, 2);
                link(mem, app_13 + 0, App(app_14));
                link(mem, app_13 + 1, Cal(0, 8, cal_21));
                u64 cal_25 = alloc(mem, 0);
                u64 cal_27 = alloc(mem, 0);
                u64 cal_29 = alloc(mem, 0);
                u64 cal_30 = alloc(mem, 0);
                u64 app_28 = alloc(mem, 2);
                link(mem, app_28 + 0, Cal(0, 8, cal_29));
                link(mem, app_28 + 1, Cal(0, 9, cal_30));
                u64 app_26 = alloc(mem, 2);
                link(mem, app_26 + 0, Cal(0, 8, cal_27));
                link(mem, app_26 + 1, App(app_28));
                u64 app_24 = alloc(mem, 2);
                link(mem, app_24 + 0, Cal(0, 40, cal_25));
                link(mem, app_24 + 1, App(app_26));
                u64 cal_31 = alloc(mem, 0);
                u64 app_23 = alloc(mem, 2);
                link(mem, app_23 + 0, App(app_24));
                link(mem, app_23 + 1, Cal(0, 9, cal_31));
                u64 cal_35 = alloc(mem, 0);
                u64 cal_37 = alloc(mem, 0);
                u64 cal_38 = alloc(mem, 0);
                u64 app_36 = alloc(mem, 2);
                link(mem, app_36 + 0, Cal(0, 8, cal_37));
                link(mem, app_36 + 1, Cal(0, 9, cal_38));
                u64 app_34 = alloc(mem, 2);
                link(mem, app_34 + 0, Cal(0, 40, cal_35));
                link(mem, app_34 + 1, App(app_36));
                u64 cal_40 = alloc(mem, 0);
                u64 cal_41 = alloc(mem, 0);
                u64 app_39 = alloc(mem, 2);
                link(mem, app_39 + 0, Cal(0, 8, cal_40));
                link(mem, app_39 + 1, Cal(0, 9, cal_41));
                u64 app_33 = alloc(mem, 2);
                link(mem, app_33 + 0, App(app_34));
                link(mem, app_33 + 1, App(app_39));
                u64 cal_45 = alloc(mem, 0);
                u64 cal_46 = alloc(mem, 0);
                u64 app_44 = alloc(mem, 2);
                link(mem, app_44 + 0, Cal(0, 40, cal_45));
                link(mem, app_44 + 1, Cal(0, 9, cal_46));
                u64 cal_48 = alloc(mem, 0);
                u64 cal_50 = alloc(mem, 0);
                u64 cal_51 = alloc(mem, 0);
                u64 app_49 = alloc(mem, 2);
                link(mem, app_49 + 0, Cal(0, 8, cal_50));
                link(mem, app_49 + 1, Cal(0, 9, cal_51));
                u64 app_47 = alloc(mem, 2);
                link(mem, app_47 + 0, Cal(0, 8, cal_48));
                link(mem, app_47 + 1, App(app_49));
                u64 app_43 = alloc(mem, 2);
                link(mem, app_43 + 0, App(app_44));
                link(mem, app_43 + 1, App(app_47));
                u64 cal_52 = alloc(mem, 0);
                u64 app_42 = alloc(mem, 2);
                link(mem, app_42 + 0, App(app_43));
                link(mem, app_42 + 1, Cal(0, 26, cal_52));
                u64 app_32 = alloc(mem, 2);
                link(mem, app_32 + 0, App(app_33));
                link(mem, app_32 + 1, App(app_42));
                u64 app_22 = alloc(mem, 2);
                link(mem, app_22 + 0, App(app_23));
                link(mem, app_22 + 1, App(app_32));
                u64 app_12 = alloc(mem, 2);
                link(mem, app_12 + 0, App(app_13));
                link(mem, app_12 + 1, App(app_22));
                u64 app_6 = alloc(mem, 2);
                link(mem, app_6 + 0, App(app_7));
                link(mem, app_6 + 1, App(app_12));
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, App(app_1));
                link(mem, app_0 + 1, App(app_6));
                u64 done = App(app_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _ITE__4_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 4);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                u64 done = Cal(4, 35, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 4);
                init = 1;
                continue;
              }
              break;
            };
            case _TAIL__SPLIT__C_: {
              if (get_tag(ask_arg(mem,term,2)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 2), 2);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 39u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 2), 2);
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
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _TWO__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 0);
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, Cal(0, 8, cal_1));
                link(mem, app_0 + 1, Cal(0, 20, cal_2));
                u64 done = App(app_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FOE__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 50, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAP__0_: {
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
                link(mem, lam_4 + 1, Cal(5, 22, cal_5));
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
            case _TAIL__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 47, cal_3));
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
            case _NIL__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 27, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2B____2_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 2);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                u64 done = Cal(2, 29, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                init = 1;
                continue;
              }
              break;
            };
            case _FIE__0_: {
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
            case _LOOP__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 42, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _PRED__SPLIT__A_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 24u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 24, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 25u)) {
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
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _CON__3_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 3);
                link(mem, ctr_0 + 0, ask_arg(mem, term, 0));
                link(mem, ctr_0 + 1, ask_arg(mem, term, 1));
                link(mem, ctr_0 + 2, ask_arg(mem, term, 2));
                u64 done = Ctr(3, 39, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _FIE__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_1 = alloc(mem, 0);
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, Cal(0, 8, cal_1));
                link(mem, app_0 + 1, ask_arg(mem, term, 0));
                u64 done = App(app_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ID__1_: {
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
            case _MAIN__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 43, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2B____0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 cal_2 = alloc(mem, 2);
                link(mem, cal_2 + 0, Var(lam_0));
                link(mem, cal_2 + 1, Var(lam_1));
                link(mem, lam_1 + 1, Cal(2, 28, cal_2));
                link(mem, lam_0 + 1, Lam(lam_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _NOT__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 33, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _NOT__SPLIT__A_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 55u)) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 56, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 57u)) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 58, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TWICE__SPLIT__A_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 24u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 24, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 25u)) {
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
                u64 cal_6 = alloc(mem, 0);
                u64 cal_8 = alloc(mem, 0);
                u64 cal_10 = alloc(mem, 0);
                u64 app_9 = alloc(mem, 2);
                link(mem, app_9 + 0, Cal(0, 14, cal_10));
                link(mem, app_9 + 1, dp1_2);
                u64 app_7 = alloc(mem, 2);
                link(mem, app_7 + 0, Cal(0, 8, cal_8));
                link(mem, app_7 + 1, App(app_9));
                u64 app_5 = alloc(mem, 2);
                link(mem, app_5 + 0, Cal(0, 8, cal_6));
                link(mem, app_5 + 1, App(app_7));
                u64 done = App(app_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _CONSUME__SPLIT__A_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 24u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 24, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 25u)) {
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
                u64 cal_6 = alloc(mem, 0);
                u64 app_5 = alloc(mem, 2);
                link(mem, app_5 + 0, Cal(0, 2, cal_6));
                link(mem, app_5 + 1, dp1_2);
                u64 done = App(app_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TEST4__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 44, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _PRED__1_: {
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
            case _HEAD__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 32, cal_3));
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
            case _POW2__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 61, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAP__5_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 5);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                link(mem, cal_0 + 3, ask_arg(mem, term, 3));
                link(mem, cal_0 + 4, ask_arg(mem, term, 4));
                u64 done = Cal(5, 38, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                init = 1;
                continue;
              }
              break;
            };
            case _HEAD__3_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 done = Cal(3, 49, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _IF_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 1u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == U32 && get_val(ask_arg(mem, term, 0)) == 0u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 2);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _TAIL__3_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 3);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                link(mem, cal_0 + 1, ask_arg(mem, term, 1));
                link(mem, cal_0 + 2, ask_arg(mem, term, 2));
                u64 done = Cal(3, 48, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                init = 1;
                continue;
              }
              break;
            };
            case _Z123X27X23X7CHX5CX65LLO__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 0);
                u64 done = Cal(0, 9, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _POW2__SPLIT__A_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 24u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 0);
                u64 app_1 = alloc(mem, 2);
                link(mem, app_1 + 0, Cal(0, 8, cal_2));
                link(mem, app_1 + 1, Ctr(0, 24, ctr_0));
                u64 done = App(app_1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 25u)) {
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
                u64 cal_6 = alloc(mem, 0);
                u64 cal_8 = alloc(mem, 0);
                u64 app_7 = alloc(mem, 2);
                link(mem, app_7 + 0, Cal(0, 13, cal_8));
                link(mem, app_7 + 1, dp1_2);
                u64 app_5 = alloc(mem, 2);
                link(mem, app_5 + 0, Cal(0, 14, cal_6));
                link(mem, app_5 + 1, App(app_7));
                u64 done = App(app_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _CONSUME__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 3, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _POW2__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 23, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _PRED__0_: {
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
            case _FUN__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_2 = alloc(mem, 0);
                u64 cal_4 = alloc(mem, 0);
                u64 cal_6 = alloc(mem, 0);
                u64 cal_8 = alloc(mem, 0);
                u64 cal_9 = alloc(mem, 0);
                u64 app_7 = alloc(mem, 2);
                link(mem, app_7 + 0, Cal(0, 8, cal_8));
                link(mem, app_7 + 1, Cal(0, 9, cal_9));
                u64 app_5 = alloc(mem, 2);
                link(mem, app_5 + 0, Cal(0, 8, cal_6));
                link(mem, app_5 + 1, App(app_7));
                u64 app_3 = alloc(mem, 2);
                link(mem, app_3 + 0, Cal(0, 7, cal_4));
                link(mem, app_3 + 1, App(app_5));
                u64 app_1 = alloc(mem, 2);
                link(mem, app_1 + 0, Cal(0, 6, cal_2));
                link(mem, app_1 + 1, App(app_3));
                u64 cal_11 = alloc(mem, 0);
                u64 cal_13 = alloc(mem, 0);
                u64 cal_15 = alloc(mem, 0);
                u64 cal_16 = alloc(mem, 0);
                u64 app_14 = alloc(mem, 2);
                link(mem, app_14 + 0, Cal(0, 8, cal_15));
                link(mem, app_14 + 1, Cal(0, 9, cal_16));
                u64 app_12 = alloc(mem, 2);
                link(mem, app_12 + 0, Cal(0, 8, cal_13));
                link(mem, app_12 + 1, App(app_14));
                u64 app_10 = alloc(mem, 2);
                link(mem, app_10 + 0, Cal(0, 10, cal_11));
                link(mem, app_10 + 1, App(app_12));
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, App(app_1));
                link(mem, app_0 + 1, App(app_10));
                u64 done = App(app_0);
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
                u64 done = Cal(0, 62, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FOE__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_3 = alloc(mem, 0);
                u64 app_2 = alloc(mem, 2);
                link(mem, app_2 + 0, Cal(0, 7, cal_3));
                link(mem, app_2 + 1, ask_arg(mem, term, 0));
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, Cal(0, 8, cal_1));
                link(mem, app_0 + 1, App(app_2));
                u64 done = App(app_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ITE__SPLIT__B_: {
              if (get_tag(ask_arg(mem,term,1)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 1), 1);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 55u)) {
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
              if ((get_tag(ask_arg(mem, term, 1)) == CTR && get_ext(ask_arg(mem, term, 1)) == 57u)) {
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
              break;
            };
            case _CON__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 lam_1 = alloc(mem, 2);
                u64 lam_2 = alloc(mem, 2);
                u64 cal_3 = alloc(mem, 3);
                link(mem, cal_3 + 0, Var(lam_0));
                link(mem, cal_3 + 1, Var(lam_1));
                link(mem, cal_3 + 2, Var(lam_2));
                link(mem, lam_2 + 1, Cal(3, 51, cal_3));
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
            case _CONSUME__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 30, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _ITE__0_: {
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
                link(mem, lam_3 + 1, Cal(4, 19, cal_4));
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
            case _ZERO__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 24, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
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
                link(mem, lam_0 + 1, Cal(1, 60, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _TWICE__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 16, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _THREE__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 0);
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, Cal(0, 8, cal_1));
                link(mem, app_0 + 1, Cal(0, 52, cal_2));
                u64 done = App(app_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _ID__0_: {
              if (1) {
                inc_cost(mem);
                u64 lam_0 = alloc(mem, 2);
                u64 cal_1 = alloc(mem, 1);
                link(mem, cal_1 + 0, Var(lam_0));
                link(mem, lam_0 + 1, Cal(1, 54, cal_1));
                u64 done = Lam(lam_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MATCH_: {
              if (1) {
                inc_cost(mem);
                u64 done = U_32(0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _TWICE__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 17, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _NOT__1_: {
              if (1) {
                inc_cost(mem);
                u64 cal_0 = alloc(mem, 1);
                link(mem, cal_0 + 0, ask_arg(mem, term, 0));
                u64 done = Cal(1, 34, cal_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TEST1__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_4 = alloc(mem, 0);
                u64 ctr_5 = alloc(mem, 0);
                u64 app_3 = alloc(mem, 2);
                link(mem, app_3 + 0, Cal(0, 18, cal_4));
                link(mem, app_3 + 1, Ctr(0, 41, ctr_5));
                u64 cal_6 = alloc(mem, 0);
                u64 app_2 = alloc(mem, 2);
                link(mem, app_2 + 0, App(app_3));
                link(mem, app_2 + 1, Cal(0, 56, cal_6));
                u64 cal_7 = alloc(mem, 0);
                u64 app_1 = alloc(mem, 2);
                link(mem, app_1 + 0, App(app_2));
                link(mem, app_1 + 1, Cal(0, 42, cal_7));
                u64 cal_8 = alloc(mem, 0);
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, App(app_1));
                link(mem, app_0 + 1, Cal(0, 58, cal_8));
                u64 done = App(app_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _HEAD__SPLIT__C_: {
              if (get_tag(ask_arg(mem,term,2)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 2), 2);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 2)) == CTR && get_ext(ask_arg(mem, term, 2)) == 39u)) {
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
                u64 done = dp1_2;
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 3);
                clear(mem, get_loc(ask_arg(mem, term, 2), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                init = 1;
                continue;
              }
              break;
            };
            case _Z__X2B____SPLIT__A_: {
              if (get_tag(ask_arg(mem,term,0)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 0), 0);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 24u)) {
                inc_cost(mem);
                u64 done = ask_arg(mem, term, 1);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 0);
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 0)) == CTR && get_ext(ask_arg(mem, term, 0)) == 25u)) {
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
                u64 cal_6 = alloc(mem, 0);
                u64 cal_9 = alloc(mem, 0);
                u64 app_8 = alloc(mem, 2);
                link(mem, app_8 + 0, Cal(0, 6, cal_9));
                link(mem, app_8 + 1, dp1_2);
                u64 app_7 = alloc(mem, 2);
                link(mem, app_7 + 0, App(app_8));
                link(mem, app_7 + 1, ask_arg(mem, term, 1));
                u64 app_5 = alloc(mem, 2);
                link(mem, app_5 + 0, Cal(0, 8, cal_6));
                link(mem, app_5 + 1, App(app_7));
                u64 done = App(app_5);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 2);
                clear(mem, get_loc(ask_arg(mem, term, 0), 0), 1);
                init = 1;
                continue;
              }
              break;
            };
            case _TRUE__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 55, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _FALSE__0_: {
              if (1) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 57, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _ONE__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_2 = alloc(mem, 0);
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, Cal(0, 8, cal_1));
                link(mem, app_0 + 1, Cal(0, 9, cal_2));
                u64 done = App(app_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 0);
                init = 1;
                continue;
              }
              break;
            };
            case _MAP__SPLIT__E_: {
              if (get_tag(ask_arg(mem,term,4)) == PAR) {
                cal_par(mem, host, term, ask_arg(mem, term, 4), 4);
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 27u)) {
                inc_cost(mem);
                u64 ctr_0 = alloc(mem, 0);
                u64 done = Ctr(0, 27, ctr_0);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 0);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                collect(mem, ask_arg(mem, term, 3));
                init = 1;
                continue;
              }
              if ((get_tag(ask_arg(mem, term, 4)) == CTR && get_ext(ask_arg(mem, term, 4)) == 39u)) {
                inc_cost(mem);
                u64 cpy_0 = ask_arg(mem, ask_arg(mem, term, 4), 2);
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
                u64 cpy_5 = ask_arg(mem, ask_arg(mem, term, 4), 1);
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
                u64 cpy_10 = ask_arg(mem, ask_arg(mem, term, 4), 0);
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
                u64 cal_23 = alloc(mem, 0);
                u64 app_22 = alloc(mem, 2);
                link(mem, app_22 + 0, Cal(0, 40, cal_23));
                link(mem, app_22 + 1, dp1_12);
                u64 app_24 = alloc(mem, 2);
                link(mem, app_24 + 0, dp0_16);
                link(mem, app_24 + 1, dp1_7);
                u64 app_21 = alloc(mem, 2);
                link(mem, app_21 + 0, App(app_22));
                link(mem, app_21 + 1, App(app_24));
                u64 cal_30 = alloc(mem, 0);
                u64 ctr_31 = alloc(mem, 0);
                u64 app_29 = alloc(mem, 2);
                link(mem, app_29 + 0, Cal(0, 21, cal_30));
                link(mem, app_29 + 1, Ctr(0, 41, ctr_31));
                u64 ctr_32 = alloc(mem, 0);
                u64 app_28 = alloc(mem, 2);
                link(mem, app_28 + 0, App(app_29));
                link(mem, app_28 + 1, Ctr(0, 41, ctr_32));
                u64 ctr_33 = alloc(mem, 0);
                u64 app_27 = alloc(mem, 2);
                link(mem, app_27 + 0, App(app_28));
                link(mem, app_27 + 1, Ctr(0, 41, ctr_33));
                u64 app_26 = alloc(mem, 2);
                link(mem, app_26 + 0, App(app_27));
                link(mem, app_26 + 1, dp1_17);
                u64 app_25 = alloc(mem, 2);
                link(mem, app_25 + 0, App(app_26));
                link(mem, app_25 + 1, dp1_2);
                u64 app_20 = alloc(mem, 2);
                link(mem, app_20 + 0, App(app_21));
                link(mem, app_20 + 1, App(app_25));
                u64 done = App(app_20);
                link(mem, host, done);
                clear(mem, get_loc(term, 0), 5);
                clear(mem, get_loc(ask_arg(mem, term, 4), 0), 3);
                collect(mem, ask_arg(mem, term, 0));
                collect(mem, ask_arg(mem, term, 1));
                collect(mem, ask_arg(mem, term, 2));
                init = 1;
                continue;
              }
              break;
            };
            case _TEST2__0_: {
              if (1) {
                inc_cost(mem);
                u64 cal_1 = alloc(mem, 0);
                u64 cal_3 = alloc(mem, 0);
                u64 cal_5 = alloc(mem, 0);
                u64 cal_7 = alloc(mem, 0);
                u64 cal_9 = alloc(mem, 0);
                u64 cal_10 = alloc(mem, 0);
                u64 app_8 = alloc(mem, 2);
                link(mem, app_8 + 0, Cal(0, 14, cal_9));
                link(mem, app_8 + 1, Cal(0, 15, cal_10));
                u64 app_6 = alloc(mem, 2);
                link(mem, app_6 + 0, Cal(0, 14, cal_7));
                link(mem, app_6 + 1, App(app_8));
                u64 app_4 = alloc(mem, 2);
                link(mem, app_4 + 0, Cal(0, 14, cal_5));
                link(mem, app_4 + 1, App(app_6));
                u64 app_2 = alloc(mem, 2);
                link(mem, app_2 + 0, Cal(0, 13, cal_3));
                link(mem, app_2 + 1, App(app_4));
                u64 app_0 = alloc(mem, 2);
                link(mem, app_0 + 0, Cal(0, 2, cal_1));
                link(mem, app_0 + 1, App(app_2));
                u64 done = App(app_0);
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
  const u64 id_to_name_size = 65;
  char* id_to_name_data[id_to_name_size];
  id_to_name_data[64] = "If";
  id_to_name_data[41] = "Matteo";
  id_to_name_data[57] = "False";
  id_to_name_data[11] = "Pred_split_a";
  id_to_name_data[25] = "Suc";
  id_to_name_data[50] = "Foe_1";
  id_to_name_data[58] = "True_0";
  id_to_name_data[62] = "Main_0";
  id_to_name_data[14] = "Twice_0";
  id_to_name_data[30] = "Consume_split_a";
  id_to_name_data[1] = "Pred_1";
  id_to_name_data[21] = "Map_0";
  id_to_name_data[53] = "Id_0";
  id_to_name_data[26] = "Nil_0";
  id_to_name_data[60] = "Suc_1";
  id_to_name_data[54] = "Id_1";
  id_to_name_data[5] = "Fun_0";
  id_to_name_data[43] = "Test4_0";
  id_to_name_data[2] = "Consume_0";
  id_to_name_data[19] = "Ite_4";
  id_to_name_data[28] = "Z_x2B__2";
  id_to_name_data[22] = "Map_5";
  id_to_name_data[39] = "Con";
  id_to_name_data[49] = "Head_split_c";
  id_to_name_data[3] = "Consume_1";
  id_to_name_data[35] = "Ite_split_b";
  id_to_name_data[61] = "Pow2_1";
  id_to_name_data[17] = "Twice_split_a";
  id_to_name_data[13] = "Pow2_0";
  id_to_name_data[51] = "Con_3";
  id_to_name_data[12] = "Test2_0";
  id_to_name_data[24] = "Zero";
  id_to_name_data[0] = "Pred_0";
  id_to_name_data[4] = "Match";
  id_to_name_data[55] = "True";
  id_to_name_data[7] = "Fie_0";
  id_to_name_data[63] = "Main";
  id_to_name_data[10] = "Foe_0";
  id_to_name_data[27] = "Nil";
  id_to_name_data[33] = "Not_1";
  id_to_name_data[59] = "Test1_0";
  id_to_name_data[47] = "Tail_3";
  id_to_name_data[32] = "Head_3";
  id_to_name_data[18] = "Ite_0";
  id_to_name_data[38] = "Map_split_e";
  id_to_name_data[48] = "Tail_split_c";
  id_to_name_data[16] = "Twice_1";
  id_to_name_data[9] = "Zero_0";
  id_to_name_data[15] = "Three_0";
  id_to_name_data[31] = "Head_0";
  id_to_name_data[42] = "Loop_0";
  id_to_name_data[45] = "Test3_0";
  id_to_name_data[40] = "Con_0";
  id_to_name_data[34] = "Not_split_a";
  id_to_name_data[23] = "Pow2_split_a";
  id_to_name_data[36] = "Not_0";
  id_to_name_data[6] = "Z_x2B__0";
  id_to_name_data[29] = "Z_x2B__split_a";
  id_to_name_data[20] = "One_0";
  id_to_name_data[44] = "Z123x27x23x7CHx5Cx65llo_0";
  id_to_name_data[56] = "False_0";
  id_to_name_data[46] = "Tail_0";
  id_to_name_data[8] = "Suc_0";
  id_to_name_data[37] = "Fie_1";
  id_to_name_data[52] = "Two_0";
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
