module Mk_quad32_1_win

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
#set-options "--z3rlimit 40"


let buffer_to_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (b:b8) = 
    B.live h b /\
    B.length b == 16
    
let post_cond (h:HS.mem) (h':HS.mem) (b:b8) =
    B.length b == 16 /\
      M.modifies (M.loc_buffer b) h h' /\
    (let old_b = buffer_to_quad32 b h  in
     let new_b = buffer_to_quad32 b h' in
     new_b == Mkfour 1 old_b.lo1 old_b.hi2 old_b.hi3)

val mk_quad32_lo0_be_1_buffer_win: b:b8 -> Stack unit
	(requires (fun h -> pre_cond h b ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 b ))
