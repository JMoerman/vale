module X64.Poly1305.Math_i

open FStar.Mul
open X64.Machine_s   // needed for nat64
open X64.Vale.Decls  // needed for shift_right64, logand64
open Poly1305.Spec_s // for modp
open X64.Vale.State_i // for add_wrap
open Opaque_i

let lowerUpper128 (l:nat64) (u:nat64) : nat128 =
    0x10000000000000000 `op_Multiply` u + l

let lowerUpper128_opaque = make_opaque lowerUpper128

let lowerUpper192 (l:nat128) (u:nat64) : int =
    0x100000000000000000000000000000000 `op_Multiply` u + l

let lowerUpper192_opaque = make_opaque lowerUpper192

let mod2_128' x:int = x % nat128_max

let mod2_128 = make_opaque mod2_128'

let modp = make_opaque modp'

// Note, we need the len parameter, as using buffer_length pushes everything into ghost, including Poly1305 spec
let heapletTo128 (s:Seq.seq nat64) (len:nat{ len % 2 == 0 /\ len <= Seq.length s}) : int->nat128 =
  fun index -> if 0 <= index && index < len / 2 then 
               (Seq.index s (2*index)) + 0x10000000000000000 * (Seq.index s (2*index + 1)) 
            else 42

let applyHeapletTo128 (s:Seq.seq nat64) (len:nat{ len % 2 == 0 /\ len <= Seq.length s}) (index:int) : nat128 =
  heapletTo128 s len index 

let rec poly1305_heap_blocks' (h:int) (pad:int) (r:int) (s:Seq.seq nat64)
        (k:int{0 <= k /\ k <= Seq.length s /\ k % 2 == 0})
        : Tot int (decreases k)
    =
    if k = 0 then h
    else
        let kk = k - 2 in
	//assert (i >= 0 ==> precedes (kk - i) (k-i));
	//assert (i < 0 ==> precedes (kk - i) (k-i));
	let hh = poly1305_heap_blocks' h pad r s kk in
        modp((hh + pad + nat64_max * (Seq.index s (kk + 1)) + (Seq.index s kk)) * r)

val poly1305_heap_blocks (h:int) (pad:int) (r:int) (s:Seq.seq nat64) 
        (k:int{0 <= k /\ k <= Seq.length s /\ k % 2 == 0}) : int

val reveal_poly1305_heap_blocks (h:int) (pad:int) (r:int) (s:Seq.seq nat64)  
        (k:int{0 <= k /\ k <= Seq.length s /\ k % 2 == 0}) : Lemma
  (requires True)
  (ensures poly1305_heap_blocks h pad r s k = poly1305_heap_blocks' h pad r s k)

val lemma_poly1305_heap_hash_blocks (h:int) (pad:int) (r:int)  (m:mem) (b:buffer64) // { buffer_length b % 2 == 0 }) 
        (len:nat{ len % 2 == 0 /\ len <= buffer_length b})
        (k:int{0 <= k /\ k <= buffer_length b /\ k % 2 == 0}) : Lemma
  (requires True)
//i <= k && k <= i + len /\
 //           (k - i) % 16 == 0 /\
 //           validSrcAddrs m i  64 ((len + 15) / 16 * 16))
           // (forall j . i <= j /\ j < i + (len + 15) / 16 * 16 && (j - i) % 8 = 0 ==> m `Map.contains` j))
  (ensures poly1305_heap_blocks h pad r (buffer64_as_seq m b) k == poly1305_hash_blocks h pad r (heapletTo128 (buffer64_as_seq m b) len) k)
          

// There are some assumptions here, which will either go away when the library switches to ints everywhere (for division too)
// or when we switch to nats (which is doable right away)
val lemma_poly_multiply : n:int -> p:pos -> r:int -> h:int -> r0:int -> r1:nat -> h0:int -> h1:int -> h2:int -> s1:int -> d0:int -> d1:int -> d2:int -> hh:int -> Lemma
  (requires 
    r1 >= 0 /\
    n > 0 /\
    4 * (n * n) == p + 5 /\
    r == r1 * n + r0 /\
    h == h2 * (n * n) + h1 * n + h0 /\
    s1 == r1 + (r1 / 4) /\
    r1 % 4 == 0 /\
    d0 == h0 * r0 + h1 * s1 /\
    d1 == h0 * r1 + h1 * r0 + h2 * s1 /\
    d2 == h2 * r0 /\
    hh == d2 * (n * n) + d1 * n + d0)
	(ensures (h * r) % p == hh % p)

// p used to be a refinement to p > 0 and h a nat.
val lemma_poly_reduce : n:int -> p:pos -> h:nat -> h2:nat -> h10:int -> c:int -> hh:int -> Lemma
  (requires
    n * n > 0 /\
    h2 >= 0 /\  // TODO: Shouldn't need to add this
    4 * (n * n) == p + 5 /\
    h2 == h / (n * n) /\
    h10 == h % (n * n) /\
    c == (h2 / 4) + (h2 / 4) * 4 /\
    hh == h10 + c + (h2 % 4) * (n * n))
  (ensures h % p == hh % p)

val lemma_poly_bits64 : u:unit -> Lemma
  (requires True)
  (ensures
    (forall (x:nat64) . {:pattern (shift_right64 x 2)} shift_right64 x 2 == x / 4) /\
    (forall (x:nat64) . {:pattern (shift_right64 x 4)} shift_right64 x 4 == x / 16) /\
    (forall (x:nat64) . {:pattern (logand64 x 3)} logand64 x 3 == x % 4) /\
    (forall (x:nat64) . {:pattern (logand64 x 15)} logand64 x 15 == x % 16) /\
    (forall (x:nat64) . {:pattern (logand64 x 0)} logand64 x 0 == 0) /\
    (forall (x:nat64) . {:pattern (logand64 x 0xffffffffffffffff)} logand64 x 0xffffffffffffffff == x) /\
    (forall (x:nat64) . {:pattern (logand64 x 0xfffffffffffffffc)} logand64 x 0xfffffffffffffffc == (x / 4) * 4) /\
    (forall (x:nat64) . {:pattern (logand64 x 0x0ffffffc0fffffff)} logand64 x 0x0ffffffc0fffffff < nat64_max / 16) /\
    (forall (x:nat64) . {:pattern (logand64 x 0x0ffffffc0ffffffc)} logand64 x 0x0ffffffc0ffffffc < nat64_max / 16) /\
    (forall (x:nat64) . {:pattern (logand64 x 0x0ffffffc0ffffffc)} (logand64 x 0x0ffffffc0ffffffc) % 4 == 0) /\
    (forall (x:nat64)  (y:nat64) . (logand64 x y) == (logand64 y x)))

val lemma_mul_strict_upper_bound : x:nat -> x_bound:int -> y:nat -> y_bound:int -> Lemma
  (requires 
    x < x_bound /\
    y < y_bound)
  (ensures x * y < x_bound * y_bound)
    
val lemma_bytes_shift_power2 : y:nat64 -> Lemma
  (requires y < 8)
  (ensures 
    shift_left64 y 3 < 64 /\
    shift_left64 y 3 == y * 8 /\
    pow2 (shift_left64 y 3) == shift_left64 1 (shift_left64 y 3))
    
val lemma_bytes_and_mod : x:nat64 -> y:nat64 -> Lemma
  (requires y < 8)
  (ensures 
    shift_left64 y 3 < 64 /\
    (let z = shift_left64 1 (shift_left64 y 3) in
     z <> 0 /\ X64.Vale.Decls.logand64 x (z-1) == x % z))

val lemma_mod_power2_lo : x0:nat64 -> x1:nat64 -> y:int -> z:int -> Lemma
  (requires 
    0 <= y /\ y < 8 /\
    z == pow2 (y * 8))
  (ensures 
    z > 0 /\
    0 <= x0 % z /\ 
    x0 % z < 0x10000000000000000 /\
    (lowerUpper128_opaque x0 x1) % z == (lowerUpper128_opaque (x0 % z) 0))
    
val lemma_power2_add64 : n:nat -> Lemma
  (requires True)
  (ensures pow2(64 + n) == 0x10000000000000000 * pow2(n))

val lemma_mod_hi : x0:nat64 -> x1:nat64 -> z:nat64 -> Lemma
  (requires z <> 0)
  (ensures
    z <> 0 /\
    lowerUpper128_opaque 0 z <> 0 /\
    (lowerUpper128_opaque x0 x1) % (lowerUpper128_opaque 0 z) == lowerUpper128_opaque x0 (x1 % z))

val lemma_poly_demod : p:pos -> h:int -> x:int -> r:int -> Lemma
  (((h % p + x) * r) % p == ((h + x) * r) % p)

val lemma_reduce128 : h:int -> h2:nat64 -> h1:nat64 -> h0:nat64 -> g:int -> g2:nat64 -> g1:nat64 -> g0:nat64 -> Lemma
  (requires h2 < 5 /\
            g == h + 5 /\
            h == lowerUpper192_opaque (lowerUpper128_opaque h0 h1) h2 /\
            g == lowerUpper192_opaque (lowerUpper128_opaque g0 g1) g2)
  (ensures
            (g2 < 4 ==> lowerUpper128_opaque h0 h1 == mod2_128 (modp h)) /\
            (g2 >= 4 ==> lowerUpper128_opaque g0 g1 == mod2_128 (modp h)))

val lemma_add_key : old_h0:nat64 -> old_h1:nat64 -> h_in:int -> key_s0:nat64 -> key_s1:nat64 -> key_s:int -> h0:nat64 -> h1:nat64 -> Lemma
  (requires h_in == lowerUpper128_opaque old_h0 old_h1 /\
            key_s == lowerUpper128_opaque key_s0 key_s1 /\
            h0 == add_wrap old_h0 key_s0 /\
            (let c = old_h0 + key_s0 >= nat64_max in
             h1 == add_wrap (add_wrap old_h1 key_s1) (if c then 1 else 0)))
  (ensures lowerUpper128_opaque h0 h1 == mod2_128 (h_in + key_s))

val lemma_lowerUpper128_and : x:nat128 -> x0:nat64 -> x1:nat64 -> y:nat128 -> y0:nat64 -> y1:nat64 -> z:nat128 -> z0:nat64 -> z1:nat64 -> Lemma
  (requires z0 == logand64 x0 y0 /\
            z1 == logand64 x1 y1 /\
            x == lowerUpper128_opaque x0 x1 /\
            y == lowerUpper128_opaque y0 y1 /\
            z == lowerUpper128_opaque z0 z1)
  (ensures z == logand128 x y)
  
val lemma_add_mod128 (x y :int) : Lemma
  (requires True)
  (ensures mod2_128 ((mod2_128 x) + y) == mod2_128 (x + y))
