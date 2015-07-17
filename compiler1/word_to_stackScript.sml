open HolKernel Parse boolLib bossLib;
val _ = new_theory "word_to_stack";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory sptreeTheory lcsymtacs miscTheory asmTheory wordLangTheory;
open stackLangTheory parmoveTheory word_allocTheory;

val _ = ParseExtras.tight_equality ();

(* TODO: move *)

val MAX_LIST_def = Define `
  (MAX_LIST [] = 0) /\
  (MAX_LIST (n::ns) = MAX n (MAX_LIST ns))`

(* -- *)

(* Here k = number of regsiters
    and f = size of stack frame
    and kf = (k,f) *)

val wReg1_def = Define `
  wReg1 r (k,f) =
    let r = r DIV 2 in
      if r < k then ([],r) else ([(k,f+k-r)],k:num)`

val wReg2_def = Define `
  wReg2 r (k,f) =
    let r = r DIV 2 in
      if r < k then ([],r) else ([(k+1,f+k-r)],k+1:num)`

val wRegImm2_def = Define `
  (wRegImm2 (Reg r) kf = let (x,n) = wReg2 r kf in (x,Reg n)) /\
  (wRegImm2 (Imm i) kf = ([],Imm i))`

val wRegWrite1_def = Define `
  wRegWrite1 g r (k,f) =
    let r = r DIV 2 in
      if r < k then g r else Seq (g k) (StackStore k (f+k-r))`

val wStackLoad_def = Define `
  (wStackLoad [] x = x) /\
  (wStackLoad ((r,i)::ps) x = Seq (StackLoad r i) (wStackLoad ps x))`

val wStackStore_def = Define `
  (wStackStore [] x = x) /\
  (wStackStore ((r,i)::ps) x = Seq (wStackStore ps x) (StackStore r i))`

val wMoveSingle_def = Define `
  wMoveSingle (x,y) (k,f) =
    case (y,x) of
    | (INL r1, INL r2) => Inst (Arith (Binop Or r1 r2 (Reg r2)))
    | (INL r1, INR r2) => StackLoad r1 (f+k-r2)
    | (INR r1, INL r2) => StackStore r2 (f+k-r1)
    | (INL r1, INL r2) => Seq (StackLoad (k+1) (f+k-r2))
                              (StackStore (k+1) (f+k-r1))`

val wMoveAux_def = Define `
  (wMoveAux [] kf = Skip) /\
  (wMoveAux [xy] kf = wMoveSingle xy kf) /\
  (wMoveAux (xy::xys) kf = Seq (wMoveSingle xy kf) (wMoveAux xys kf))`

val pair_swap_def = Define `
  pair_swap (x,y) = (y DIV 2, x DIV 2)`

val format_var_def = Define `
  (format_var k NONE = INL (k+1)) /\
  (format_var k (SOME x) = if x < k:num then INL x else INR x)`;

val format_result_def = Define `
  format_result k (y,x) = (format_var k x, format_var k y)`;

val wMove_def = Define `
  wMove xs (k,f) =
    wMoveAux (MAP (format_result k) (parmove (MAP pair_swap xs))) (k,f)`;

val wInst_def = Define `
  (wInst Skip kf = Inst Skip) /\
  (wInst (Const n c) kf =
    wRegWrite1 (\n. Inst (Const n c)) n kf) /\
  (wInst (Arith (Binop bop n1 n2 (Imm imm))) kf =
    wRegWrite1 (\n1. Inst (Arith (Binop bop n1 n2 (Imm imm)))) n1 kf) /\
  (wInst (Arith (Binop bop n1 n2 (Reg n3))) kf =
    wRegWrite1 (\n1. Inst (Arith (Binop bop n1 n2 (Reg n3)))) n1 kf) /\
  (wInst (Arith (Shift sh n1 n2 a)) kf =
    wRegWrite1 (\n1. Inst (Arith (Shift sh n1 n2 a))) n1 kf) /\
  (wInst (Mem mop n1 (Addr n2 offset)) kf =
    wRegWrite1 (\n1. Inst (Mem mop n1 (Addr n2 offset))) n1 kf)`

val wImpossible_def = Define `
  wImpossible = Skip:'a stackLang$prog`

val bits_to_word_def = Define `
  (bits_to_word [] = 0w) /\
  (bits_to_word (T::xs) = (bits_to_word xs << 1 || 1w)) /\
  (bits_to_word (F::xs) = (bits_to_word xs << 1))`;

val word_list_def = tDefine "word_list" `
  word_list (xs:bool list) d =
    if LENGTH xs < d \/ (d = 0) then [bits_to_word xs]
    else bits_to_word (TAKE d xs ++ [T]) :: word_list (DROP d xs) d`
 (WF_REL_TAC `measure (LENGTH o FST)`
  \\ fs [LENGTH_DROP] \\ DECIDE_TAC)

val write_bitmap_def = Define `
  (write_bitmap live k f):'a word list =
    let names = MAP (\(r,y). f+k-r) (toAList live) in
      word_list (GENLIST (\x. MEM x names) f) (dimindex(:'a) - 1)`

val wLiveAux_def = tDefine "wLiveAux" `
  wLiveAux (xs:'a word list) r index =
    case xs of
    | [] => Skip
    | [x] => Seq (Inst (Const r x)) (StackStore r index)
    | _ => Seq (wLiveAux [HD xs] r index)
               (wLiveAux (TL xs) r (index+1))`
 (WF_REL_TAC `measure (LENGTH o FST)` \\ fs [] \\ decide_tac);

val wLive_def = Define `
  wLive live (k,f) = wLiveAux (write_bitmap live k f) k 0`;

val SeqStackFree_def = Define `
  SeqStackFree n p = if n = 0 then p else Seq (StackFree n) p`

val CallAny_def = Define `
  (CallAny ret (SOME pos) args handler kf =
     Call ret (INL pos) handler) /\
  (CallAny ret NONE args handler kf =
     let (x1,r) = wReg1 (LAST args) kf in
       wStackLoad x1 (Call ret (INR r) handler))`

val stack_arg_count_def = Define `
  stack_arg_count dest arg_count k =
    case dest of
    | SOME _ => (arg_count - k:num)
    | NONE => ((arg_count - 1) - k:num)`

val stack_free_def = Define `
  stack_free dest arg_count (k,f) =
    f - stack_arg_count dest arg_count k`

val stack_move_def = Define `
  (stack_move 0 k1 k2 i p = p) /\
  (stack_move (SUC n) k1 k2 i p =
     Seq (stack_move n (k1+1) (k2+1) i p)
         (Seq (StackLoad i k1) (StackStore i k2)))`

val StackArgs_def = Define `
  StackArgs dest arg_count (k,f) =
    let n = stack_arg_count dest arg_count k in
      stack_move n f 0 k (StackAlloc n)`

val comp_def = Define `
  (comp (Skip:'a wordLang$prog) kf = Skip:'a stackLang$prog) /\
  (comp (Move _ xs) kf = wMove xs kf) /\
  (comp (Inst i) kf = wInst i kf) /\
  (comp (Return v1 v2) kf =
     let (xs,x) = wReg1 v1 kf in
       wStackLoad xs (SeqStackFree (SND kf) (Return x 1))) /\
  (comp (Raise v) kf = Call NONE (INL 0) NONE) /\
  (comp (Tick) kf = Tick) /\
  (comp (Seq p1 p2) kf =
     let q2 = comp p2 kf in
     let q1 = comp p1 kf in
       Seq q1 q2) /\
  (comp (If cmp r ri p1 p2) kf =
     let (x1,r') = wReg1 r kf in
     let (x2,ri') = wRegImm2 ri kf in
       wStackLoad (x1++x2) (If cmp r' ri' (comp p1 kf) (comp p2 kf))) /\
  (comp (Set name exp) kf =
     case exp of
     | Var n => let (x1,r') = wReg1 n kf in wStackLoad x1 (Set name r')
     | _ => wImpossible) /\
  (comp (Get n name) kf =
     wRegWrite1 (\r. Get r name) n kf) /\
  (comp (Call ret dest args handler) kf =
     case ret of
     | NONE => SeqStackFree (stack_free dest (LENGTH args - 1) kf)
                 (CallAny NONE dest (TL args) NONE kf)
     | SOME (ret_var, live, ret_code, l1, l2) =>
         case handler of
         | NONE => Seq (wLive live kf)
                     (Seq (StackArgs dest (LENGTH args) kf)
                          (CallAny (SOME (comp ret_code kf,l1,l2))
                             dest args NONE kf))
         | SOME (handle_var, handle_code, h1, h2) => Skip (* TODO *)) /\
  (comp (Alloc size live) kf =
     (Seq (wLive live kf) (Alloc size))) /\
  (comp _ kf = wImpossible)`

val raise_stub_def = Define `
  raise_stub k =
     Seq (Get k Handler)
    (Seq (StackSetSize k)
    (Seq (StackLoad k 2) (* next handler *)
    (Seq (Set Handler k)
    (Seq (StackLoad k 1) (* handler pc *)
    (Seq (StackFree 3)
         (Raise k))))))`;

val compile_def = Define `
  compile (prog:'a wordLang$prog) arg_count reg_count =
    let stack_arg_count = arg_count - reg_count in
    let stack_var_count = MAX (max_var prog DIV 2 - reg_count) stack_arg_count in
      if stack_var_count = 0 then
        comp prog (reg_count,0)
      else
        let bitmap_size = stack_var_count DIV (dimindex (:'a) - 1) + 1 in
        let f = stack_var_count + bitmap_size in
          Seq (StackAlloc (f - stack_arg_count)) (comp prog (reg_count,f))`

val _ = export_theory();
