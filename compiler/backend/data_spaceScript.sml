(*
  This dataLang phase lumps together MakeSpace operations. Each
  MakeSpace operations corresponds to a memory allocation in the later
  wordLang code. By lumping together MakeSpace operations we turn
  several calls to the memory allocator into a single efficient call.
*)
open preamble dataLangTheory;
local open backend_commonTheory in end

val _ = new_theory "data_space";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val alloc_size_def = Define
  `alloc_size word_size arch_size = if word_size <= arch_size - 2 then 0 else (ROUNDUP_DIV word_size arch_size)+1`

val op_space_req_def = Define `
  (op_space_req (Cons _) l _ = if l = 0n then 0 else l+1) /\
  (op_space_req Ref l _ = l + 1) /\
  (op_space_req (WordOp sz _) _ arch_size = alloc_size sz arch_size) /\
  (op_space_req (WordShift sz _ _) _ arch_size = alloc_size sz arch_size) /\
  (op_space_req (WordFromInt sz) _ arch_size = alloc_size sz arch_size) /\
  (op_space_req (WordToInt sz) _ arch_size = alloc_size sz arch_size) /\
  (op_space_req (WordToWord _ dest) _ arch_size = alloc_size dest arch_size) /\
  (op_space_req (FP_uop _) v9 _ = 3) /\
  (op_space_req (FP_bop _) v9 _ = 3) /\
  (op_space_req (FP_top _) v9 _ = 3) /\
  (op_space_req _ _ _ = 0)`;

(*
Theorem op_space_req_pmatch:
  !op l.
  op_space_req op l =
    case op of
      Cons _ => if l = 0n then 0 else l+1
    | Ref => l + 1
    | WordOp W64 _ => 3
    | WordShift W64 _ _ => 3
    | WordFromInt => 3
    | WordToInt => 3
    | WordFromWord b => (if b then 0 else 3)
    | FP_uop _ => 3
    | FP_bop _ => 3
    | _ => 0
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> fs[op_space_req_def]
QED
*)

val pMakeSpace_def = Define `
  (pMakeSpace (INL c) = c) /\
  (pMakeSpace (INR (k,names,c)) = Seq (MakeSpace k names) c)`;

val space_def = Define `
  (space (MakeSpace k names) _ = INR (k,names,Skip)) /\
  (space (Seq c1 c2) arch_size =
     let d1 = pMakeSpace (space c1 arch_size) in
     let x2 = space c2 arch_size in
       dtcase x2 of
       | INL c4 =>
          (dtcase c1 of
           | MakeSpace k names => INR (k,names,c4)
           | Skip => INL c4
           | _ => INL (Seq d1 c4))
       | INR (k2,names2,c4) =>
          (dtcase c1 of
           | Skip => INR (k2,names2,c4)
           | MakeSpace k1 names1 => INR (k2,inter names1 names2,c4)
           | Move dest src =>
               INR (k2,insert src () (delete dest names2),
                    Seq (Move dest src) c4)
           | Assign dest op args NONE =>
               INR (op_space_req op (LENGTH args) arch_size + k2,
                    list_insert args (delete dest names2),
                    Seq (Assign dest op args NONE) c4)
           | _ => INL (Seq d1 (pMakeSpace x2)))) /\
  (space (If n c2 c3) arch_size =
     INL (If n (pMakeSpace (space c2 arch_size)) (pMakeSpace (space c3 arch_size)))) /\
  (space c _ = INL c)`;

Theorem space_pmatch:
  ∀c.
  space c arch_size =
    case c of
    | MakeSpace k names => INR (k,names,Skip)
    | Seq c1 c2 => (
     let d1 = pMakeSpace (space c1 arch_size) in
     let x2 = space c2 arch_size in
       case x2 of
       | INL c4 =>
          (case c1 of
           | MakeSpace k names => INR (k,names,c4)
           | Skip => INL c4
           | _ => INL (Seq d1 c4))
       | INR (k2,names2,c4) =>
          (case c1 of
           | Skip => INR (k2,names2,c4)
           | MakeSpace k1 names1 => INR (k2,inter names1 names2,c4)
           | Move dest src =>
               INR (k2,insert src () (delete dest names2),
                    Seq (Move dest src) c4)
           | Assign dest op args NONE =>
               INR (op_space_req op (LENGTH args) arch_size + k2,
                    list_insert args (delete dest names2),
                    Seq (Assign dest op args NONE) c4)
           | _ => INL (Seq d1 (pMakeSpace x2))))
    | If n c2 c3 =>
      INL (If n (pMakeSpace (space c2 arch_size)) (pMakeSpace (space c3 arch_size)))
    | c => INL c
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac >> TRY(PURE_REWRITE_TAC [LET_DEF] >> BETA_TAC))
  >> fs[space_def]
QED

val compile_def = Define `
  compile c arch_size = pMakeSpace (space c arch_size)`;

val _ = export_theory();
