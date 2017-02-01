#ifndef __KREMLIB_H
#define __KREMLIB_H

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdbool.h>
#include <time.h>

// For types and values from C.fsti that do not exactly have the same name as
// their C counterparts
extern int exit_success;
extern int exit_failure;

typedef uint64_t FStar_UInt64_t, FStar_UInt64_t_;
typedef int64_t FStar_Int64_t, FStar_Int64_t_;
typedef uint32_t FStar_UInt32_t, FStar_UInt32_t_;
typedef int32_t FStar_Int32_t, FStar_Int32_t_;
typedef uint16_t FStar_UInt16_t, FStar_UInt16_t_;
typedef int16_t FStar_Int16_t, FStar_Int16_t_;
typedef uint8_t FStar_UInt8_t, FStar_UInt8_t_;
typedef int8_t FStar_Int8_t, FStar_Int8_t_;

#if defined(__GNUC__) && defined(__SIZEOF_INT128__)
typedef __int128 FStar_UInt128_t, FStar_UInt128_t_;
#define FStar_UInt128_add(x,y) ((x) + (y))
#define FStar_UInt128_mul(x,y) ((x) * (y))
#define FStar_UInt128_add_mod(x,y) ((x) + (y))
#define FStar_UInt128_sub(x,y) ((x) - (y))
#define FStar_UInt128_sub_mod(x,y) ((x) - (y))
#define FStar_UInt128_logand(x,y) ((x) & (y))
#define FStar_UInt128_logor(x,y) ((x) | (y))
#define FStar_UInt128_logxor(x,y) ((x) ^ (y))
#define FStar_UInt128_lognot(x) (~(x))
#define FStar_UInt128_shift_left(x, y) ((x) << (y))
#define FStar_UInt128_shift_right(x, y) ((x) >> (y))
#define FStar_Int_Cast_uint64_to_uint128(x) ((__int128)(x))
#define FStar_Int_Cast_uint128_to_uint64(x) ((uint64_t)(x))
#define FStar_UInt128_mul_wide(x, y) ((__int128)(x) * (y))
#else
typedef struct {
  uint64_t high;
  uint64_t low;
} FStar_UInt128_t, FStar_UInt128_t_;
FStar_UInt128_t FStar_UInt128_add(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_add_mod(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_sub(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_sub_mod(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_mul(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_logand(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_logor(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_logxor(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_lognot(FStar_UInt128_t x);
FStar_UInt128_t FStar_UInt128_shift_left(FStar_UInt128_t x, FStar_UInt32_t y);
FStar_UInt128_t FStar_UInt128_shift_right(FStar_UInt128_t x, FStar_UInt32_t y);
FStar_UInt128_t FStar_Int_Cast_uint64_to_uint128(uint64_t x);
uint64_t FStar_Int_Cast_uint128_to_uint64(FStar_UInt128_t x);
FStar_UInt128_t FStar_UInt128_mul_wide(uint64_t x, uint64_t y);
#endif

// Constant-time comparisons
uint64_t FStar_UInt64_eq_mask(uint64_t x, uint64_t y);
uint64_t FStar_UInt64_gte_mask(uint64_t x, uint64_t y);
uint32_t FStar_UInt32_eq_mask(uint32_t x, uint32_t y);
uint32_t FStar_UInt32_gte_mask(uint32_t x, uint32_t y);
uint8_t FStar_UInt8_eq_mask(uint8_t x, uint8_t y);
uint8_t FStar_UInt8_gte_mask(uint8_t x, uint8_t y);

// 128-bit arithmetic
FStar_UInt128_t FStar_UInt128_eq_mask(FStar_UInt128_t x, FStar_UInt128_t y);
FStar_UInt128_t FStar_UInt128_gte_mask(FStar_UInt128_t x, FStar_UInt128_t y);

// Buffers (FIXME remove eqb!)
#define FStar_Buffer_eqb(b1, b2, n) \
  (memcmp((b1), (b2), (n)*sizeof((b1)[0])) == 0)
void FStar_Buffer_recall(void *x);

// Some types that KreMLin has no special knowledge of; many of them appear in
// signatures of ghost functions, meaning that it suffices to give them (any)
// definition.
typedef void *Prims_pos, *Prims_nat, *Prims_nonzero, *FStar_Seq_Base_seq, *Prims_int,
        *Prims_prop,
        *FStar_HyperStack_mem, *FStar_Set_set, *Prims_st_pre_h, *FStar_Heap_heap,
        *Prims_all_pre_h, *FStar_TSet_set, *Prims_string, *Prims_list,
        *FStar_Map_t,
        *FStar_UInt63_t_, *FStar_Int63_t_,
        *FStar_UInt63_t, *FStar_Int63_t,
        *FStar_UInt_uint_t, *FStar_Int_int_t,
        *FStar_HyperStack_stackref, *FStar_Bytes_bytes,
        *FStar_HyperHeap_rid, *FStar_Heap_aref;

// Prims; all of the functions below abort;
bool Prims_op_GreaterThanOrEqual(Prims_int x, Prims_int y);
bool Prims_op_LessThanOrEqual(Prims_int x, Prims_int y);
bool Prims_op_GreaterThan(Prims_int x, Prims_int y);
bool Prims_op_LessThan(Prims_int x, Prims_int y);
Prims_int Prims_pow2(Prims_int x);
Prims_int Prims_op_Multiply(Prims_int x, Prims_int y);
Prims_int Prims_op_Addition(Prims_int x, Prims_int y);
Prims_int Prims_op_Subtraction(Prims_int x, Prims_int y);
Prims_int Prims_op_Division(Prims_int x, Prims_int y);
Prims_int Prims_op_Modulus(Prims_int x, Prims_int y);
void *Prims_magic(void *_);
void *Prims_admit(void *x);
void *Prims____Cons___tl(void *_);

// Note: it's possible to define a statement that always exits cleanly, but
// Kremlin generates calls to KRML_EABORT and it's not possible (as far as I
// know) to define an expression that has a "universal size" and aborts when
// evaluated...
#define KRML_EXIT \
  do { \
    printf("Unimplemented function at %s:%d\n", __FILE__, __LINE__); \
    exit(254); \
  } while (0)

#define KRML_EABORT \
  (exit(252), 0)

// Stubs to make ST happy
bool FStar_HyperStack_is_eternal_color(Prims_int x0);
#define FStar_ST_op_Colon_Equals(x, v) KRML_EXIT
#define FStar_ST_op_Bang(x) 0
#define FStar_ST_salloc(x) 0
#define FStar_ST_ralloc(x,y) 0
#define FStar_ST_new_region(x) 0
#define FStar_ST_recall(x) do {} while (0)
#define FStar_ST_recall_region(x) do {} while (0)

#define FStar_Monotonic_RRef_m_recall(...) do {} while (0)
#define FStar_Monotonic_RRef_m_write(...) do {} while (0)
#define FStar_Monotonic_RRef_m_alloc(...) { 0 }

#define FStar_HyperHeap_root 0

// Misc; many of these are polymorphic, hence not extracted (yet) by Kremlin,
// which means that a macro is the "right" way to make they don't generate a
// compilation error.
Prims_int FStar_UInt32_v(uint32_t x);
#define Prims_fst(x) (x).fst
#define Prims_snd(x) (x).snd
#define FStar_Seq_Base_createEmpty(x) 0
#define FStar_Seq_Base_create(len, init) 0
#define FStar_Seq_Base_upd(s, i, e) 0
#define FStar_Seq_Base_eq(l1, l2) 0
FStar_Seq_Base_seq FStar_Seq_Base_append(FStar_Seq_Base_seq x, FStar_Seq_Base_seq y);
FStar_Seq_Base_seq FStar_Seq_Base_slice(FStar_Seq_Base_seq x, FStar_Seq_Base_seq y, Prims_nat z);
#define FStar_Seq_Properties_snoc(x, y) 0
#define FStar_Seq_Properties_cons(x, y) 0
#define FStar_Seq_Base_index(x, y) 0
FStar_UInt32_t FStar_UInt32_uint_to_t(Prims_nat x);

#endif
