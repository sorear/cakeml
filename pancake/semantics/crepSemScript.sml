(*
  Semantics of crepLang
*)

open preamble crepLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           panSemTheory (* for word_lab datatype  *)
           ffiTheory in end;

val _ = new_theory"crepSem";
val _ = set_grammar_ancestry [
  "crepLang", "alignment",
  "finite_map", "misc", "wordLang", "panSem", "ffi"]

(* re-defining them again to avoid varname from panSem *)
Type varname = ``:num``
Type funname = ``:mlstring``

Datatype:
  state =
    <| locals      : varname |-> 'a word_lab
     ; globals     : 5 word  |-> 'a word_lab
     ; code        : funname |-> (varname list # ('a crepLang$prog))
                   (* arguments, body *)
     ; memory      : 'a word -> 'a word_lab
     ; memaddrs    : ('a word) set
     ; clock       : num
     ; be          : bool
     ; ffi         : 'ffi ffi_state |>
End

val state_component_equality = theorem"state_component_equality";

Datatype:
  result = Error
         | TimeOut
         | Break
         | Continue
         | Return    ('a word_lab)
         | Exception ('a word_lab)
         | FinalFFI final_event
End

val s = ``(s:('a,'ffi) crepSem$state)``

Definition mem_load_def:
  mem_load (addr:'a word) ^s =
    if addr IN s.memaddrs
    then SOME (s.memory addr) else NONE
End


Definition set_var_def:
  set_var v w ^s =
    (s with locals := s.locals |+ (v,w))
End

(* gv: global variable *)
Definition set_globals_def:
  set_globals gv w ^s =
    (s with globals := s.globals |+ (gv,w))
End

Definition upd_locals_def:
   upd_locals varargs ^s =
     s with <| locals := FEMPTY |++ varargs  |>
End

Definition empty_locals_def:
   empty_locals ^s =
     s with <| locals := FEMPTY |>
End

Definition lookup_code_def:
  lookup_code code fname args len =
    case (FLOOKUP code fname) of
      | SOME (ns, prog) =>
         if LENGTH ns = LENGTH args
         then SOME (prog, alist_to_fmap (ZIP (ns,args))) else NONE
      | _ => NONE
End

Definition eval_def:
  (eval (s:('a,'ffi) crepSem$state) ((Const w):'a crepLang$exp) = SOME (Word w)) ∧
  (eval s (Var v) = FLOOKUP s.locals v) ∧
  (eval s (Label fname) =
   case FLOOKUP s.code fname of
    | SOME _ => SOME (Label fname)
    | _ => NONE) /\
  (eval s (Load addr) =
    case eval s addr of
     | SOME (Word w) => mem_load w s
     | _ => NONE) /\
  (eval s (LoadByte addr) =
    case eval s addr of
     | SOME (Word w) =>
        (case mem_load_byte s.memory s.memaddrs s.be w of
           | NONE => NONE
           | SOME w => SOME (Word (w2w w)))
     | _ => NONE) /\
  (eval s (LoadGlob gadr) = FLOOKUP (s.globals) gadr) ∧
  (eval s (Op op es) =
    case (OPT_MMAP (eval s) es) of
     | SOME ws =>
       if (EVERY (\w. case w of (Word _) => T | _ => F) ws)
       then OPTION_MAP Word
            (word_op op (MAP (\w. case w of Word n => n) ws)) else NONE
      | _ => NONE) /\
  (eval s (Cmp cmp e1 e2) =
    case (eval s e1, eval s e2) of
     | (SOME (Word w1), SOME (Word w2)) => SOME (Word (v2w [word_cmp cmp w1 w2]))
     | _ => NONE) /\
  (eval s (Shift sh e n) =
    case eval s e of
     | SOME (Word w) => OPTION_MAP Word (word_sh sh w n)
     | _ => NONE)
Termination
  wf_rel_tac `measure (exp_size ARB o SND)`
  \\ rpt strip_tac \\ imp_res_tac MEM_IMP_exp_size
  \\ TRY (first_x_assum (assume_tac o Q.SPEC `ARB`))
  \\ decide_tac
End

Definition dec_clock_def:
  dec_clock ^s =
   s with clock := s.clock - 1
End

Definition fix_clock_def:
  fix_clock old_s (res, new_s) =
    (res, new_s with <|clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock |>)
End

Theorem fix_clock_IMP_LESS_EQ:
  !x. fix_clock ^s x = (res,s1) ==> s1.clock <= s.clock
Proof
  full_simp_tac(srw_ss())[fix_clock_def,FORALL_PROD] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> decide_tac
QED


Definition res_var_def:
  (res_var lc (n, NONE) = lc \\ n) /\
  (res_var lc (n, SOME v) = lc |+ (n,v))
End

Definition evaluate_def:
  (evaluate (Skip:'a crepLang$prog,^s) = (NONE,s)) /\
  (evaluate (Dec v e prog, s) =
    case (eval s e) of
     | SOME value =>
        let (res,st) = evaluate (prog,s with locals := s.locals |+ (v,value)) in
        (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v))
        | NONE => (SOME Error, s)) ∧
  (evaluate (Assign v src,s) =
    case (eval s src) of
    | NONE => (SOME Error, s)
    | SOME w =>
       case FLOOKUP s.locals v of
        | SOME _ => (NONE, s with locals := s.locals |+ (v,w))
        | _ => (SOME Error, s)) /\
  (evaluate (Store dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (Word adr), SOME w) =>
        (case mem_store adr w s.memaddrs s.memory of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (StoreByte dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (Word adr), SOME (Word w)) =>
        (case mem_store_byte s.memory s.memaddrs s.be adr (w2w w) of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (StoreGlob dst src,s) =
    case eval s src of
     | SOME w => (NONE, set_globals dst w s)
     | _ => (SOME Error, s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
     if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If e c1 c2,s) =
    case (eval s e) of
     | SOME (Word w) =>
        evaluate (if w <> 0w then c1 else c2, s)  (* False is 0, True is everything else *)
     | _ => (SOME Error,s)) /\
  (evaluate (Break,s) = (SOME Break,s)) /\
  (evaluate (Continue,s) = (SOME Continue,s)) /\
  (evaluate (While e c,s) =
    case (eval s e) of
     | SOME (Word w) =>
       if (w <> 0w) then
        let (res,s1) = fix_clock s (evaluate (c,s)) in
           case res of
           | SOME Continue =>
             if s1.clock = 0 then (SOME TimeOut,empty_locals s1)
             else evaluate (While e c,dec_clock s1)
           | NONE =>
             if s1.clock = 0 then (SOME TimeOut,empty_locals s1)
             else evaluate (While e c,dec_clock s1)
           | SOME Break => (NONE,s1)
           | _ => (res,s1)
       else (NONE,s)
    | _ => (SOME Error,s)) /\
  (evaluate (Return e,s) =
    case (eval s e) of
     | SOME w => (SOME (Return w),empty_locals s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise e,s) =
    case (eval s e) of
     | SOME w => (SOME (Exception w), empty_locals s)
     | _ => (SOME Error,s)) /\
 (evaluate (Tick,s) =
   if s.clock = 0 then (SOME TimeOut,empty_locals s)
   else (NONE,dec_clock s)) /\
 (evaluate (Call caltyp trgt argexps,s) =
   case (eval s trgt, OPT_MMAP (eval s) argexps) of
    | (SOME (Label fname), SOME args) =>
       (case lookup_code s.code fname args (LENGTH args) of
         | SOME (prog, newlocals) => if s.clock = 0 then (SOME TimeOut,empty_locals s) else
           let eval_prog = fix_clock ((dec_clock s) with locals:= newlocals)
                                     (evaluate (prog, (dec_clock s) with locals:= newlocals)) in
           (case eval_prog of
              | (NONE,st) => (SOME Error,s)
              | (SOME Break,st) => (SOME Error,s)
              | (SOME Continue,st) => (SOME Error,s)
              | (SOME (Return retv),st) =>
                  (case caltyp of
                    | Tail    => (SOME (Return retv),st)
                    | Ret rt  => (NONE, set_var rt retv (st with locals := s.locals))
                    | Handle rt evar p => (NONE, set_var rt retv (st with locals := s.locals)))
              | (SOME (Exception exn),st) =>
                  (case caltyp of
                    | Tail    => (SOME (Exception exn),st)
                    | Ret rt  => (SOME (Exception exn), st with locals := s.locals)
                    | Handle rt evar p =>  evaluate (p, set_var evar exn (st with locals := s.locals)))
              | (res,st) =>
                  (case caltyp of
                    | Tail => (res,st)
                    | _  => (res,st with locals := s.locals)))
         | _ => (SOME Error,s))
    | (_, _) => (SOME Error,s)) /\
  (evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2,s) =
   case (FLOOKUP s.locals len1, FLOOKUP s.locals ptr1, FLOOKUP s.locals len2, FLOOKUP s.locals ptr2) of
    | SOME (Word w),SOME (Word w2),SOME (Word w3),SOME (Word w4) =>
       (case (read_bytearray w2 (w2n w) (mem_load_byte s.memory s.memaddrs s.be),
              read_bytearray w4 (w2n w3) (mem_load_byte s.memory s.memaddrs s.be)) of
         | SOME bytes,SOME bytes2 =>
            (case call_FFI s.ffi ffi_index bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome),s)
              | FFI_return new_ffi new_bytes =>
                (case write_bytearray w4 new_bytes s.memory s.memaddrs s.be of
                  | SOME m => (NONE, s with <| memory := m;ffi := new_ffi |>)
                  | NONE => (SOME Error,s)))
         | _ => (SOME Error,s))
       | res => (SOME Error,s))
Termination
  wf_rel_tac `(inv_image (measure I LEX measure (prog_size (K 0)))
               (\(xs,^s). (s.clock,xs)))` >>
  rpt strip_tac >> TRY (full_simp_tac(srw_ss())[] >> DECIDE_TAC) >>
  imp_res_tac fix_clock_IMP_LESS_EQ >> full_simp_tac(srw_ss())[] >>
  imp_res_tac (GSYM fix_clock_IMP_LESS_EQ) >>
  full_simp_tac(srw_ss())[set_var_def,set_globals_def,upd_locals_def,dec_clock_def, LET_THM] >>
  rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  decide_tac
End


Theorem evaluate_clock:
   !prog s r s'. (evaluate (prog,s) = (r,s')) ==>
                 s'.clock <= s.clock
Proof
  (*recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ rw [] \\ every_case_tac
  \\ fs [set_var_def, mem_store_def,call_env_def,dec_clock_def, LET_THM]
  \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rveq
  \\ imp_res_tac fix_clock_IMP_LESS_EQ
  \\ imp_res_tac LESS_EQ_TRANS \\ fs []*)
  cheat
QED

val fix_clock_evaluate = Q.prove(
  `fix_clock s (evaluate (prog,s)) = evaluate (prog,s)`,
  Cases_on `evaluate (prog,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock \\ fs [GSYM NOT_LESS, state_component_equality]);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();
