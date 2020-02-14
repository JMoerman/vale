module Atmel.Print_s

// Trusted code for producing assembly code

open FStar.Mul
open Atmel.Machine_s
open Atmel.Semantics_s
open FStar.IO

noeq type printer = {
  reg_prefix : unit -> string;
  mem_prefix : string -> string;
  maddr      : string -> option (string & string) -> string -> string;
  const      : int -> string;
  ins_name   : string -> list reg -> string;
  op_order   : string -> string -> string & string;
  align      : unit -> string;
  header     : unit -> string;
  footer     : unit -> string;
  proc_name  : string -> string;
  ret        : string -> string;
}

let print_reg_name (r:reg) =
  match r with
  | R0 -> "r0"
  | R1 -> "r1"
  | R2 -> "r2"
  | R3 -> "r3"
  | R4 -> "r4"
  | R5 -> "r5"
  | R6 -> "r6"
  | R7 -> "r7"
  | R8  -> "r8"
  | R9  -> "r9"
  | R10 -> "r10"
  | R11 -> "r11"
  | R12 -> "r12"
  | R13 -> "r13"
  | R14 -> "r14"
  | R15 -> "r15"

let print_reg (r:reg) (p:printer) =
  p.reg_prefix() ^ print_reg_name r

let print_maddr (m:maddr) (ptr_type:string) (reg_printer:reg->printer->string) (p:printer) =
  p.mem_prefix ptr_type ^
  (match m with
     | MConst n -> p.const n
     | MReg r offset -> p.maddr (reg_printer r p) None (string_of_int offset)
     | MIndex base scale index offset ->
          p.maddr (reg_printer base p)
          (Some (string_of_int scale, reg_printer index p))
          (string_of_int offset)
   )
open FStar.UInt64

let print_imm8 (i:int) (p:printer) =
  p.const i

assume val print_any: 'a -> string

let print_ins (ins:ins) (p:printer) =
  let print_pair (dst src:string) =
    let (first, second) = p.op_order dst src in
      first ^ ", " ^ second
  in
  let print_op_pair (dst:reg) (src:reg) (print_dst:reg->printer->string) (print_src:reg->printer-> string) =
    print_pair (print_dst dst p) (print_src src p)
  in
  let print_ops (dst:reg) (src:reg) =
    print_op_pair dst src print_reg print_reg
  in
  match ins with
  | Mov8 rd rr ->       p.ins_name "  mov" [rd; rr] ^ print_ops rd rr
  | LoadImm8 rd k ->    p.ins_name "  ldi" [rd] ^ print_reg_name rd ^ print_imm8 k p
  | Mul8 rd rr ->       p.ins_name "  mul" [rd; rr] ^ print_ops rd rr
  | Add8 rd rr ->       p.ins_name "  add" [rd; rr] ^ print_ops rd rr
  | AddCarry8 rd rr ->  p.ins_name "  adc" [rd; rr] ^ print_ops rd rr
  | Sub8 rd rr ->       p.ins_name "  sub" [rd; rr] ^ print_ops rd rr
  | SubBorrow8 rd rr -> p.ins_name "  sbc" [rd; rr] ^ print_ops rd rr
  | SubImm8 rd k ->     p.ins_name "  subi" [rd] ^ print_reg_name rd ^ print_imm8 k p
  | SubCImm8 rd k ->    p.ins_name "  sbci" [rd] ^ print_reg_name rd ^ print_imm8 k p
  | Neg rd ->           p.ins_name "  neg" [rd] ^ print_reg_name rd
  | Inc rd ->           p.ins_name "  inc" [rd] ^ print_reg_name rd
  | Dec rd ->           p.ins_name "  dec" [rd] ^ print_reg_name rd
  | Mov16 rd rr ->      p.ins_name "  movw" [rd; rr] ^ print_ops rd rr

let print_cmp (c:ocmp) (counter:int) (p:printer) : string =
  match c with
  | OBrne -> " brne " ^ "L" ^ string_of_int counter ^ "\n"

let rec print_block (b:codes) (n:int) (p:printer) : string & int =
  match b with
  | Nil -> ("", n)
  | head :: tail ->
    let (head_str, n') = print_code head n p in
    let (rest, n'') = print_block tail n' p in
    (head_str ^ rest, n'')
and print_code (c:code) (n:int) (p:printer) : string & int =
  match c with
  | Ins ins -> (print_ins ins p ^ "\n", n)
  | Block b -> print_block b n p

let print_header (p:printer) =
  print_string (p.header())

let print_proc (name:string) (code:code) (label:int) (p:printer) : FStar.All.ML int =
  let proc = p.proc_name name in
  let (code_str, final_label) = print_code code label p in
  let ret = p.ret name in
  print_string (proc ^ code_str ^ ret);
  final_label

let print_footer (p:printer) =
  print_string (p.footer())


// Concrete printers for MASM and GCC syntax
let masm : printer =
  let reg_prefix unit = "" in
  let mem_prefix (ptr_type:string) = ptr_type ^ " ptr " in
  let maddr (base:string) (adj:option (string & string)) (offset:string) =
    match adj with
    | None -> "[" ^ base ^ " + " ^ offset ^ "]"
    | Some (scale, index) -> "[" ^ base ^ " + " ^ scale ^ " * " ^ index ^ " + " ^ offset ^ "]"
  in
  let const (n:int) = string_of_int n in
  let ins_name (name:string) (ops:list reg) : string = name ^ " " in
  let op_order dst src = (dst, src) in
  let align() = "ALIGN" in
  let header() = ".code\n" in
  let footer() = "end\n" in
  let proc_name (name:string) = "ALIGN 16\n" ^ name ^ " proc\n" in
  let ret (name:string) = "  ret\n" ^ name ^ " endp\n" in
  {
    reg_prefix = reg_prefix;
    mem_prefix = mem_prefix;
    maddr      = maddr;
    const      = const;
    ins_name   = ins_name;
    op_order   = op_order;
    align      = align;
    header     = header;
    footer     = footer;
    proc_name  = proc_name;
    ret        = ret;
  }

let gcc : printer =
  let reg_prefix unit = "%" in
  let mem_prefix (ptr_type:string) = "" in
  let maddr (base:string) (adj:option (string & string)) (offset:string) =
    match adj with
    | None -> offset ^ "(" ^ base ^ ")"
    | Some (scale, index) -> offset ^ " (" ^ base ^ ", " ^ scale ^ ", " ^ index ^ ")"
  in
  let const (n:int) = "$" ^ string_of_int n in
  let rec ins_name (name:string) (ops:list reg) : string = name ^ " " in
  let op_order dst src = (src, dst) in
  let align() = ".align" in
  let header() = ".text\n" in
  let footer() = "\n" in
  let proc_name (name:string) = ".global " ^ name ^ "\n" ^ name ^ ":\n" in
  let ret (name:string) = "  ret\n\n" in
  {
    reg_prefix = reg_prefix;
    mem_prefix = mem_prefix;
    maddr      = maddr;
    const      = const;
    ins_name   = ins_name;
    op_order   = op_order;
    align      = align;
    header     = header;
    footer     = footer;
    proc_name  = proc_name;
    ret        = ret;
  }
