(*
  Correctness proofs for floating-point optimizations
*)
open source_rewriterTheory source_to_sourceTheory fpOptTheory fpOptPropsTheory
     fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
     semanticsTheory semanticsPropsTheory
     evaluatePropsTheory terminationTheory fpSemPropsTheory;
open preamble;

val _ = new_theory "source_to_sourceProofs";

(**
  Helper theorems and definitions
**)
val isPureOp_simp =
  LIST_CONJ (map (fn (t, c) => EVAL (``isPureOp ^t``))
    (isPureOp_def |> concl |> dest_forall |> snd
                  |> dest_eq |> snd |> TypeBase.dest_case |> #3));

(* TODO: Move, from Konrad Slind *)
load "Unify";
fun join_hyps th =
 let open pairSyntax
     val (asl,c) = dest_thm th
     val frozen = free_varsl asl
     val ants = fst(strip_imp (snd (strip_forall c)))
     val eqns = filter is_eq ants
     val (L,R) = unzip (map dest_eq eqns)
     val theta = Unify.simp_unify_terms frozen
                        (list_mk_pair L) (list_mk_pair R)
 in
   SIMP_RULE std_ss [] (GEN_ALL (INST theta (SPEC_ALL th)))
 end

Theorem do_if_cases:
  do_if x e1 e2 = SOME e ==> e = e1 \/ e = e2
Proof
  fs[do_if_def] \\ TOP_CASE_TAC \\ fs[]
QED

Theorem isPureExpList_app[simp]:
  ! es1 es2. isPureExpList (es1 ++ es2) = (isPureExpList es1 /\ isPureExpList es2)
Proof
  Induct_on `es1` \\ fs[isPureExp_def]
  \\ rpt gen_tac
  \\ EQ_TAC \\ fs[]
QED

Theorem isPureExpList_reverse[simp]:
  isPureExpList (REVERSE es) = isPureExpList es
Proof
  Induct_on `es` \\ fs[isPureExp_def]
  \\ rpt gen_tac \\ EQ_TAC \\ simp[]
QED

(**
  First, we prove that pure expressions ignore their FFI.
  This allows to swap out the FFI with an arbitrary different one
  and get the same one back from evaluating
**)

Theorem isPureOp_same_ffi:
  ! refs1 (ffi1 ffi2 : 'a ffi_state) op vl refs2 r.
    isPureOp op /\
    do_app (refs1, ffi1) op vl = SOME ((refs2,ffi2), r) ==>
    ! refs (ffi:'a ffi_state).
      do_app (refs, ffi) op vl = SOME ((refs, ffi), r)
Proof
  Cases_on `op` \\ rpt gen_tac
  \\ TRY (fs[isPureOp_simp, do_app_def] \\ rpt (TOP_CASE_TAC \\ fs[]) \\ NO_TAC)
QED

local
  val pmatch_goal =
    ``\ env refs1 p v vl.
        ! r.
        pmatch env refs1 p v vl = r ==>
        isPurePat p ==>
        ! refs2. pmatch env refs2 p v vl = r``
  val pmatch_list_goal =
    ``\ env refs1 pl v vl.
        ! r.
        pmatch_list env refs1 pl v vl = r ==>
        isPurePatList pl ==>
        ! refs2. pmatch_list env refs2 pl v vl = r``
  val indThm = pmatch_ind |> ISPEC pmatch_goal |> SPEC pmatch_list_goal
in
Theorem isPurePat_ignores_ref:
  (! env refs1 p v vl.
    ^pmatch_goal env refs1 p v vl)
  /\
  (! env refs1 pl v vl.
    ^pmatch_list_goal env refs1 pl v vl)
Proof
  match_mp_tac indThm
  \\ rpt strip_tac
  \\ fs[isPurePat_def, pmatch_def] \\ rpt (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac \\ fs[]
QED
end

val semState_comp_eq = semanticPrimitivesTheory.state_component_equality;

Theorem can_pmatch_all_same_ffi:
  isPurePatExpList pes /\
  can_pmatch_all env refs (MAP FST pes) v ==>
  ! refs2. can_pmatch_all env refs2 (MAP FST pes) v
Proof
  Induct_on `pes` \\ fs[can_pmatch_all_def]
  \\ rpt gen_tac \\ rpt (disch_then assume_tac)
  \\ Cases_on `h` \\ fs[isPureExp_def]
  \\ metis_tac [isPurePat_ignores_ref]
QED

local
  val eval_goal =
    ``\ (s1:'a semanticPrimitives$state) env expl.
        ! s2 r.
          evaluate s1 env expl = (s2, r) ==>
          isPureExpList expl /\
          r <> Rerr (Rabort Rtype_error) ==>
          ! (s:'a semanticPrimitives$state).
            s.fp_state.rws = s1.fp_state.rws /\
            s.fp_state.canOpt = s1.fp_state.canOpt /\
            (! x. x <= (s2.fp_state.choices - s1.fp_state.choices) ==>
              s.fp_state.opts x = s1.fp_state.opts x) ==>
            ? fpOpts.
              evaluate s env expl =
                (s with <| fp_state := s.fp_state with
                  <| opts := fpOpts; choices := s.fp_state.choices + (s2.fp_state.choices - s1.fp_state.choices)|> |>, r)``;
  val eval_match_goal =
    ``\ (s1:'a semanticPrimitives$state) env v pl err_v.
        ! s2 r.
          isPurePatExpList pl /\
          evaluate_match s1 env v pl err_v = (s2, r) ==>
          r <> Rerr (Rabort Rtype_error) ==>
          ! (s:'a semanticPrimitives$state).
            s.fp_state.rws = s1.fp_state.rws /\
            s.fp_state.canOpt = s1.fp_state.canOpt /\
            (! x. x <= (s2.fp_state.choices - s1.fp_state.choices) ==>
              s.fp_state.opts x = s1.fp_state.opts x) ==>
              ? fpOpts.
              evaluate_match s env v pl err_v =
                (s with <| fp_state := s.fp_state with
                  <| opts := fpOpts; choices := s.fp_state.choices + (s2.fp_state.choices - s1.fp_state.choices)|> |>, r)``;
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal
  val isPureExpList_single_thm =
    SIMP_RULE std_ss [] (EVAL ``isPureExpList [e] = isPureExp e``);
  val isPureExpList_Cons_thm =
    SIMP_RULE std_ss [] (EVAL ``isPureExpList (e::es) = (isPureExp e /\ isPureExpList es)``);
  val resolve_simple =
    fn thm => mp_tac thm \\ rpt (disch_then (fn dThm => first_assum (mp_then Any mp_tac dThm)));
  val fp_inv_tac =
    rpt strip_tac
    \\ imp_res_tac evaluate_fp_opts_inv \\ rveq
    \\ rpt (qpat_x_assum `! x. _ x = _ x` (fn thm => fs[GSYM thm]));
  val trivial =
    rpt strip_tac \\ rveq \\ fs[]
    \\ res_tac
    \\ qexists_tac `fpOpts'`
    \\ fs[fpState_component_equality, semState_comp_eq];
in
Theorem isPureExpList_swap_ffi:
  (! s1 env expl.
    ^eval_goal s1 env expl) /\
  (! s1 env v pl err_v.
    ^eval_match_goal s1 env v pl err_v)
Proof
  irule indThm \\ rpt gen_tac \\ rpt conj_tac
  \\ rpt gen_tac \\ rpt strip_tac \\ fs[]
  \\ simp[evaluate_def, isPureExp_def]
  \\ rpt strip_tac
  \\ fs[isPureExpList_single_thm]
  \\ TRY (first_x_assum irule \\ fs[Once isPureExp_def] \\ NO_TAC)
  \\ TRY (fs[fpState_component_equality, semState_comp_eq] \\ NO_TAC)
  \\ TRY (qpat_x_assum `_ = (_, _)` mp_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac
    \\ last_x_assum (qspec_then `s` resolve_simple)
    \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ fs[]
    \\ rename [`do_if (HD r) e2 e3 = SOME eR`]
    \\ `isPureExp eR` by (imp_res_tac do_if_cases \\ fs[])
    \\ res_tac \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate s_fpNew env [_]`
    \\ first_x_assum (qspec_then `s_fpNew` resolve_simple)
    \\ unabbrev_all_tac \\ fs[semState_comp_eq]
    \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ trivial)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspec_then `s` impl_subgoal_tac)
    \\ TRY (rpt conj_tac \\ fp_inv_tac \\ NO_TAC)
    \\ fs[]
    \\ rpt (first_x_assum (fn ithm => first_x_assum (fn thm => mp_then Any assume_tac thm ithm)))
    \\ qmatch_goalsub_abbrev_tac `evaluate s_fpNew env _`
    \\ first_x_assum (qspecl_then [`s_fpNew`] resolve_simple)
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ fs[fpState_component_equality, semState_comp_eq])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspecl_then [`s`] resolve_simple)
    \\ disch_then impl_subgoal_tac
    >- (rpt conj_tac \\ fp_inv_tac)
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate_match s_fpNew env _ _ _`
    \\ first_x_assum impl_subgoal_tac >- fs[]
    \\ first_x_assum (qspecl_then [`s_fpNew`] resolve_simple)
    \\ imp_res_tac can_pmatch_all_same_ffi \\ fs[]
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ fp_inv_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- (rpt strip_tac \\ rveq \\ fs[]
        \\ first_x_assum drule
        \\ disch_then (qspecl_then
            [`s with fp_state := s.fp_state with canOpt := case annot of Opt => T | NoOpt => F`] impl_subgoal_tac)
        >- (fs[fpState_component_equality])
        \\ fs[fpState_component_equality, semState_comp_eq])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ res_tac
    \\ last_x_assum (qspecl_then [`s with fp_state := s.fp_state with canOpt := case annot of Opt => T | NoOpt => F`] assume_tac)
    \\ fs[fpState_component_equality]
    \\ res_tac \\ fs[fpState_component_equality, semState_comp_eq])
  >- (TOP_CASE_TAC \\ rpt strip_tac \\ rveq
      \\ fs[fpState_component_equality, semState_comp_eq])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ first_x_assum drule
    \\ impl_tac \\ fs[]
    \\ TRY (fp_inv_tac \\ NO_TAC)
    \\ disch_then assume_tac \\ fs[fpState_component_equality, semState_comp_eq]
    \\ rename [`do_log lop (HD v) e2 = SOME (Exp eR)`]
    \\ `eR = e2`
        by (qpat_x_assum `do_log _ _ _ = SOME (Exp eR)` mp_tac
            \\ fs[do_log_def]
            \\ rpt (TOP_CASE_TAC \\ fs[]))
    \\ rveq
    \\ first_x_assum drule \\ disch_then assume_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate s_fpNew env _ = _`
    \\ first_x_assum (qspecl_then [`s_fpNew`] impl_subgoal_tac)
    \\ unabbrev_all_tac
    >- (fs[] \\ fp_inv_tac)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ fp_inv_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    >- (rveq \\ fs[isPureOp_def])
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
    \\ imp_res_tac isPureOp_same_ffi
    \\ first_x_assum (qspecl_then [`s`] assume_tac)
    \\ rename [`evaluate st env (REVERSE es) = (s2, Rval _)`]
    \\ TOP_CASE_TAC \\ Cases_on `s.fp_state.canOpt` \\ fs[] \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
    \\ first_x_assum impl_subgoal_tac
    \\ TRY (fp_inv_tac)
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ fs[shift_fp_opts_def, semState_comp_eq, fpState_component_equality]
    \\ rpt (qpat_x_assum `! x. _ x = _ x` ( fn thm => fs[GSYM thm])))
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ first_x_assum drule \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ fs[fpState_component_equality, semState_comp_eq])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ rpt strip_tac \\ fs[]
    \\ first_x_assum (qspecl_then [`s`] impl_subgoal_tac)
    >- fp_inv_tac
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate s_fpNew _ _ = _`
    \\ first_x_assum impl_subgoal_tac \\ fs[]
    \\ first_x_assum (qspecl_then [`s_fpNew`] impl_subgoal_tac)
    \\ unabbrev_all_tac
    >- fp_inv_tac
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ fp_inv_tac)
  >- (
    ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ fs[]
    \\ imp_res_tac (hd (CONJ_LIST 2 (EVAL_RULE isPurePat_ignores_ref)))
    \\ fs[])
QED
end

Theorem isPureExp_same_ffi:
  ! st1 st2 env fps1 fps2 e r.
    isPureExp e /\
    r <> Rerr (Rabort Rtype_error) /\
    evaluate st1 env [e] = (st2, r) ==>
    st2 = st1 with fp_state := st2.fp_state
Proof
  rpt strip_tac
  \\ first_assum (mp_then Any assume_tac (CONJUNCT1 (SIMP_RULE std_ss [] isPureExpList_swap_ffi)))
  \\ first_x_assum (qspecl_then [`st1`] impl_subgoal_tac)
  \\ fs[isPureExp_def] \\ fs[fpState_component_equality, semState_comp_eq]
QED

val prep = fn thm => SIMP_RULE std_ss [] thm;

(**
  Putting it all together: For a pure expression that returns a value,
  we can a) change to an arbitrary state,
  b) append an optimization,
  c) pick an arbitrary oracle to return in the end
  This is the key lemma for proving correctness of Icing optimizations
**)
Theorem isPureExp_evaluate_change_oracle:
  ! (st1 st2:'a semanticPrimitives$state) env e r.
    isPureExp e /\
    evaluate st1 env [e] = (st2, Rval r) ==>
    ! opt (stN1:'a semanticPrimitives$state) g.
      (stN1.fp_state.canOpt <=> st1.fp_state.canOpt) ==>
      ? oracle.
        evaluate (stN1 with fp_state := stN1.fp_state with <| rws := st1.fp_state.rws ++ [opt]; opts := oracle |>) env [e] =
          (stN1 with fp_state := stN1.fp_state with <| rws := st1.fp_state.rws ++ [opt]; opts := g; choices := stN1.fp_state.choices + (st2.fp_state.choices - st1.fp_state.choices) |>, Rval r)
Proof
  rpt strip_tac
  (* This will come in handy later to finish the proof
     The final fs call will not conclude without this assumption being proven! *)
  \\ `st1.fp_state.choices <= st2.fp_state.choices`
      by (imp_res_tac (CONJUNCT1 evaluate_fp_opts_inv)
          \\ fs[fpState_component_equality])
  (* Append the optimization *)
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
  \\ first_x_assum (qspecl_then [`[opt]`, `g`] assume_tac) \\ fs[]
  (* Change the global state *)
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 isPureExpList_swap_ffi)))
  \\ fs[isPureExp_def]
  \\ first_x_assum (qspecl_then [`stN1 with fp_state := stN1.fp_state with <| rws := st1.fp_state.rws ++ [opt]; opts := fpOpt |>`] impl_subgoal_tac)
  \\ fs[]
  (* Change the resulting opts function to an arbitrary one *)
  \\ first_x_assum (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok))
  \\ fs[fpState_component_equality]
  \\ qexists_tac `optUntil (st2.fp_state.choices - st1.fp_state.choices) fpOpt g`
  \\ first_x_assum (qspec_then `g` assume_tac)
  \\ imp_res_tac (CONJUNCT1 evaluate_fp_opts_inv)
  \\ fs[fpState_component_equality]
QED

Theorem fp_add_comm_cases:
  !e fpBop.
    (? e1 e2.
      e = (App (FP_bop fpBop) [e1; e2]) /\
      isPureExp e /\
      rewriteFPexp [fp_comm_gen fpBop] (App (FP_bop fpBop) [e1; e2]) =
        App (FP_bop fpBop) [e2; e1]) \/
    (rewriteFPexp [fp_comm_gen fpBop] e = e)
Proof
  rpt gen_tac \\ Cases_on `e`
  \\ fs[fp_comm_gen_def, rewriteFPexp_def, isPureExp_def, matchesFPexp_def]
  \\ rename1 `App op els`
  \\ Cases_on `op` \\ fs[isPureOp_def]
  \\ Cases_on `fpBop` \\ fs[] \\ EVAL_TAC
QED

Theorem fp_state_opts_eq[local]:
  fps with <| rws := rwsN; opts := fps.opts |> = fps with <| rws := rwsN |>
Proof
  Cases_on `fps` \\ fs[fpState_component_equality]
QED

Theorem do_app_fp_inv:
  do_app (refs, ffi) (FP_bop op) [v1; v2] = SOME ((refs2, ffi2), r) ==>
    ? w1 w2.
      fp_translate v1 = SOME (FP_WordTree w1) /\ fp_translate v2 = SOME (FP_WordTree w2) /\
      r = Rval (FP_WordTree (fp_bop op w1 w2))
Proof
  Cases_on `op` \\ every_case_tac \\ fs[do_app_def] \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq \\ fs[]
QED

Theorem nth_len:
  nth (l ++ [x]) (LENGTH l + 1) = SOME x
Proof
  Induct_on `l` \\ fs[fpOptTheory.nth_def, ADD1]
QED

(* Correctness definition for rewriteFPexp *)
Definition is_rewriteFPexp_correct_def:
  is_rewriteFPexp_correct rws (st1:'a semanticPrimitives$state) st2 env e r =
      ((evaluate st1 env [rewriteFPexp rws e] = (st2, r) /\
        st1.fp_state.canOpt) ==>
      ? fpOpt fpOptR.
        evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env [e] =
          (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r))
End

Definition is_rewriteFPexp_list_correct_def:
  is_rewriteFPexp_list_correct rws (st1:'a semanticPrimitives$state) st2 env exps r =
      ((evaluate st1 env (MAP (rewriteFPexp rws) exps) = (st2, r) /\
       st1.fp_state.canOpt)==>
      ? fpOpt fpOptR.
        evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env exps =
          (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r))
End

Theorem empty_rw_correct:
   ! (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct [] st1 st2 env e r
Proof
  rpt strip_tac \\ fs[is_rewriteFPexp_correct_def, rewriteFPexp_def]
  \\ rpt strip_tac \\ qexists_tac `st1.fp_state.opts` \\ qexists_tac `st2.fp_state.opts`
  \\ `st1 = st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws; opts := st1.fp_state.opts |>`
      by (fs[semState_comp_eq, fpState_component_equality])
  \\ pop_assum (fn thm => fs[GSYM thm])
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

local
  val fp_rws_append_comm =
    SIMP_RULE std_ss [] evaluate_fp_rws_append
    |> CONJ_LIST 2
    |> map (SPEC_ALL) |> map (GEN ``(opts:(fp_pat #fp_pat) list)``)
    |> map (Q.SPEC `[fp_comm_gen fpBop]`) |> map GEN_ALL
    |> LIST_CONJ;
  val eval_fp_opt_inv =
    SIMP_RULE std_ss [] fpSemPropsTheory.evaluate_fp_opts_inv
    |> CONJ_LIST 2 |> hd;
  val isPureExp_ignores_state =
    EVAL_RULE isPureExpList_swap_ffi
    |> CONJ_LIST 2
    |> hd
in
Theorem fp_comm_gen_correct:
  ! fpBop (st1 st2:'a semanticPrimitives$state) env e res.
  is_rewriteFPexp_correct [fp_comm_gen fpBop] st1 st2 env e (Rval res)
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qspecl_then [`e`, `fpBop`] assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_add_comm_cases)
  \\ fs[]
  >- (
    pop_assum (fn thm => fs[thm])
    \\ imp_res_tac fp_rws_append_comm
    \\ first_x_assum (qspecl_then [`g`, `fpBop`] assume_tac) \\ fs[]
    \\ first_x_assum (mp_then Any (qspec_then `g` assume_tac) (CONJUNCT1 optUntil_evaluate_ok))
    \\ fs[fpState_component_equality]
    \\ asm_exists_tac \\ fs[])
  \\ fs[evaluate_def] \\ rveq
  \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ rename [`evaluate st1 env [e1]`]
  \\ Cases_on `evaluate st1 env [e1]` \\ fs[]
  \\ rename [`evaluate st1 env [e1] = (st2, r)`]
  \\ Cases_on `r` \\ fs[]
  \\ rename [`evaluate st1 env [e1] = (st2, Rval r)`]
  \\ rename [`evaluate st2 env [e2]`]
  \\ Cases_on `evaluate st2 env [e2]` \\ fs[]
  \\ rename [`evaluate st2 env [e2] = (st3, r)`] \\ Cases_on `r` \\ fs[]
  \\ rename [`evaluate st2 env [e2] = (st3, Rval r)`]
  \\ fs[astTheory.isFpOp_def, astTheory.isFpBool_def]
  \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ `st3.fp_state.canOpt` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ `st2 = st1 with fp_state := st2.fp_state /\ st3 = st1 with fp_state := st3.fp_state`
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[semState_comp_eq])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[shift_fp_opts_def]
  \\ rename [`evaluate st1 env [e1] = (st2, Rval [r1])`, `evaluate st2 env [e2] = (st3, Rval [r2])`]
  \\ Cases_on `do_app (st3.refs, st3.ffi) (FP_bop fpBop) [r2; r1]` \\ fs[]
  \\ PairCases_on `x` \\ fs[]
  \\ imp_res_tac do_app_fp_inv \\ rveq \\ fs[]
  \\ rpt strip_tac \\ rveq
  \\ ntac 2 (first_x_assum (fn thm => (mp_then Any assume_tac isPureExp_evaluate_change_oracle thm) \\ mp_tac thm))
  \\ rpt (disch_then assume_tac)
  \\ first_x_assum
      (qspecl_then
        [`fp_comm_gen fpBop`,
         `st1 with fp_state := st2.fp_state with choices := st1.fp_state.choices + (st3.fp_state.choices - st2.fp_state.choices)`,
         `\x. if (x = 0)
              then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
                (case do_fprw (Rval (FP_WordTree (fp_bop fpBop w1 w2))) (st3.fp_state.opts x) st3.fp_state.rws of | NONE => [] | SOME r_opt => st3.fp_state.opts x)
              else g (x - 1)`]
      impl_subgoal_tac)
  >- (fs[isPureExp_def]
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ first_x_assum (qspecl_then [`fp_comm_gen fpBop`, `st1`, `oracle`] impl_subgoal_tac)
  >- (fs[isPureExp_def]
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ `st1.fp_state.rws = st2.fp_state.rws` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ qexists_tac `oracle'` \\ fs[]
  \\ `st1 with fp_state  := st2.fp_state with
        <| rws := st2.fp_state.rws ++ [fp_comm_gen fpBop];
           opts := oracle;
           choices := st1.fp_state.choices + (st3.fp_state.choices - st2.fp_state.choices) |> =
      st1 with fp_state := st1.fp_state with
        <| rws := st2.fp_state.rws ++ [fp_comm_gen fpBop];
           opts := oracle;
           choices := st1.fp_state.choices + (st3.fp_state.choices - st2.fp_state.choices) |>`
    by (fs[fpState_component_equality, semState_comp_eq]
        \\ imp_res_tac evaluate_fp_opts_inv \\ fs[]
        \\ simp[FUN_EQ_THM])
  \\ pop_assum (fn thm => fs[thm])
  \\ `st2.fp_state.canOpt` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ imp_res_tac isPureOp_same_ffi \\ fs[isPureOp_def]
  \\ first_x_assum (qspecl_then [`st1.refs`, `st1.ffi`] assume_tac)
  \\ fs[list_result_def]
  \\ fs[do_app_def, shift_fp_opts_def, fpState_component_equality]
  \\ qexists_tac `\x. g x`
  \\ rpt conj_tac
  >- (imp_res_tac evaluate_fp_opts_inv
      \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
  \\ fs[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ fs[EVAL ``rwFp_pathWordTree (fp_comm_gen fpBop) Here (fp_bop fpBop w2 w1)``, instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st3.fp_state.opts 0) st3.fp_state.rws (fp_bop fpBop w1 w2)` \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_comm_gen fpBop]` assume_tac)
  \\ `st3.fp_state.rws = st2.fp_state.rws` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
QED
end

Theorem rewriteExp_compositional:
  ! rws opt.
   (! (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct rws st1 st2 env e r) /\
   (! (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct [opt] st1 st2 env e r) ==>
  ! (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct ([opt] ++ rws) st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ PairCases_on `opt` \\ simp[rewriteFPexp_def]
  \\ reverse TOP_CASE_TAC \\ fs[]
  >- (
    rpt strip_tac
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [`[(opt0, opt1)] ++ rws`, `g`] assume_tac) \\ fs[]
    \\ asm_exists_tac \\ fs[])
  \\ TOP_CASE_TAC \\ fs[]
  >- (
    rpt strip_tac
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [`[(opt0, opt1)] ++ rws`, `\x. []`] assume_tac) \\ fs[]
    \\ fs[fpState_component_equality] \\ asm_exists_tac \\ fs[])
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      rpt strip_tac
      \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [`[(opt0, opt1)]`, `\x. []`] assume_tac) \\ fs[]
      \\ first_x_assum (fn thm => (first_x_assum (fn ithm => mp_then Any impl_subgoal_tac ithm thm)))
      \\ fs[fpState_component_equality] \\ asm_exists_tac \\ fs[])
    \\ rpt strip_tac \\ fs[]
    \\ first_x_assum drule \\ fs[state_component_equality, fpState_component_equality]
    \\ disch_then assume_tac \\ fs[] \\ pop_assum mp_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate st1N env [_] = (st2N, r)`
    \\ disch_then assume_tac
    \\ first_x_assum (qspecl_then [`st1N`, `st2N`, `env`, `e`, `r`] assume_tac)
    \\ fs[rewriteFPexp_def] \\ rfs[]
    \\ unabbrev_all_tac \\ fs[state_component_equality, fpState_component_equality]
    \\ first_x_assum impl_subgoal_tac \\ fs[]
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_up)))
    \\ first_x_assum (qspec_then `st1.fp_state.rws  ++ [(opt0, opt1)] ++ rws` impl_subgoal_tac)
    >- (fs[SUBSET_DEF] \\ rpt strip_tac \\ fs[])
    \\ fs[] \\ qexists_tac `fpOpt''` \\ qexists_tac `fpOpt2`
    \\ fs[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_fp_opts_inv
QED

Theorem lift_rewriteFPexp_correct_list:
  ! rws (st1 st2:'a semanticPrimitives$state) env exps r.
    (! (st1 st2: 'a semanticPrimitives$state) env e r.
      is_rewriteFPexp_correct rws st1 st2 env e r) ==>
  is_rewriteFPexp_list_correct rws st1 st2 env exps r
Proof
  Induct_on `exps` \\ fs[is_rewriteFPexp_correct_def, is_rewriteFPexp_list_correct_def, semState_comp_eq, fpState_component_equality]
  \\ rpt strip_tac \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ simp[Once evaluate_cons]
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  >- (rpt strip_tac \\ rveq
      \\ first_x_assum (qspecl_then [`st1`, `q`, `env`, `h`, `Rerr e`] impl_subgoal_tac)
      \\ simp[Once evaluate_cons]
      \\ fs[]  \\ qexists_tac `fpOpt` \\ fs[]
      \\ qexists_tac `fpOptR` \\ fs[])
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ first_assum (qspecl_then [`st1`, `q`, `env`, `h`, `Rval a`] impl_subgoal_tac)
  \\ simp[Once evaluate_cons] \\ fs[]
  \\ first_x_assum (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok))
  \\ last_x_assum drule
  \\ disch_then drule
  \\ disch_then assume_tac \\ fs[]
  \\ first_x_assum impl_subgoal_tac
  \\ TRY (imp_res_tac evaluate_fp_opts_inv\\ NO_TAC)
  \\ fs[]
  \\ first_x_assum (qspec_then `fpOpt'` assume_tac) \\ fs[]
  \\ qexists_tac `optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'` \\ qexists_tac `fpOptR` \\ fs[]
QED

Definition is_optimise_correct_def:
  is_optimise_correct rws (st1:'a semanticPrimitives$state) st2 env cfg exps r =
    (evaluate st1 env (MAP (optimise (cfg with optimisations := rws)) exps) = (st2, r) ==>
    ? fpOpt fpOptR.
      evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env exps =
        (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r))
End

Theorem MAP_FST_optimise:
  MAP FST (MAP (\ (p, e). (p, optimise cfg e)) l) = MAP FST l
Proof
  Induct_on `l` \\ fs[] \\ rpt strip_tac \\ PairCases_on `h` \\ fs[]
QED

local
  val eval_goal =
  ``\ (st1: 'ffi semanticPrimitives$state) env exps.
    ! cfg rws st2 r expsN.
      evaluate st1 env exps = (st2, r) /\
      (! st1 st2 env exps r. is_rewriteFPexp_list_correct rws st1 st2 env exps r) /\
      exps = MAP (optimise (cfg with optimisations := rws)) expsN ==>
      ? fpOpt fpOptR.
      evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env expsN =
        (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r)``
  val eval_match_goal =
    ``\ (st1: 'ffi semanticPrimitives$state) env v pl err_v.
      ! cfg rws st2 r plN.
        evaluate_match st1 env v pl err_v = (st2, r) /\
        (! st1 st2 env exps r. is_rewriteFPexp_list_correct rws st1 st2 env exps r) /\
        pl = MAP (\ (p, e). (p, optimise (cfg with optimisations := rws) e)) plN ==>
        ? fpOpt fpOptR.
        evaluate_match (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env v plN err_v =
        (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r)``
in
Theorem foo:
  (! st1 env exps.
    ^eval_goal st1 env exps) /\
  (! (st1:'ffi semanticPrimitives$state) env v pl err_v.
      ^eval_match_goal st1 env v pl err_v)
Proof
  ho_match_mp_tac (terminationTheory.evaluate_ind |> ISPEC eval_goal |> SPEC eval_match_goal)
  \\ rpt strip_tac \\ fs[semState_comp_eq, fpState_component_equality] \\ rpt strip_tac
  \\ TRY (qpat_x_assum `evaluate _ _ _ = _` mp_tac)
  (* e1::e2::en *)
  >- (
    Cases_on `expsN` \\ fs[]
    \\ Cases_on `t` \\ fs[] \\ rveq
    \\ simp [Once evaluate_cons]
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- (rpt strip_tac \\ rveq \\ fs[PULL_EXISTS]
        \\ first_x_assum drule
        \\ disch_then (qspecl_then [`cfg`, `h`] impl_subgoal_tac) \\ fs[]
        \\ qexists_tac `fpOpt` \\ qexists_tac `fpOptR` \\ simp[Once evaluate_cons])
    \\ ntac 2 (TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ last_x_assum drule
    \\ disch_then (qspecl_then [`cfg`, `h`] impl_subgoal_tac) \\ fs[]
    \\ first_x_assum (mp_then Any mp_tac (CONJUNCT1 optUntil_evaluate_ok))
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`cfg`, `h'::t'`] impl_subgoal_tac) \\ fs[optimise_def]
    \\ disch_then (qspec_then `fpOpt'` assume_tac)
    \\ qexists_tac `optUntil (q.fp_state.choices - st.fp_state.choices) fpOpt fpOpt'` \\ simp[Once evaluate_cons]
    \\ fs[semState_comp_eq, fpState_component_equality])
  (* Lit l *)
  >- (
    rveq \\ Cases_on `x0` \\ fs[optimise_def] \\ rveq
    >- (rpt strip_tac \\ fs[evaluate_def, semState_comp_eq, fpState_component_equality])
    \\ Cases_on `cfg.canOpt` \\ fs[]
    (* by assumption *) \\ cheat)
  (* Raise e *)
  >- (
    rveq \\ Cases_on `x0` \\ fs[optimise_def] \\ rveq
    >- (
      fs[evaluate_def, semState_comp_eq, fpState_component_equality, PULL_EXISTS]
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ rveq
      \\ res_tac \\ fs[]
      \\ first_x_assum (qspecl_then [`e'`, `cfg`] impl_subgoal_tac) \\ fs[]
      \\ qexists_tac `fpOpt` \\ fs[semState_comp_eq, fpState_component_equality])
    \\ Cases_on `cfg.canOpt` \\ fs[]
    (* by assumption *) \\ cheat )
  (* Handle e pl *)
  >- (
    rveq \\ Cases_on `x0` \\ fs[optimise_def] \\ rveq
    >- (
      fs[evaluate_def, semState_comp_eq, fpState_component_equality, PULL_EXISTS]
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      >- (
        rpt strip_tac \\ rveq
        \\ res_tac \\ fs[]
        \\ first_x_assum (qspecl_then [`e'`, `cfg`] impl_subgoal_tac) \\ fs[]
        \\ qexists_tac `fpOpt` \\ fs[semState_comp_eq, fpState_component_equality])
      \\ reverse TOP_CASE_TAC \\ fs[]
      >- (
        rpt strip_tac \\ rveq
        \\ res_tac \\ fs[]
        \\ first_x_assum (qspecl_then [`e'`, `cfg`] impl_subgoal_tac) \\ fs[]
        \\ qexists_tac `fpOpt` \\ fs[semState_comp_eq, fpState_component_equality])
      \\ reverse TOP_CASE_TAC \\ fs[MAP_FST_optimise]
      >- (
       rpt strip_tac \\ rveq
       \\ res_tac \\ fs[]
       \\ first_x_assum (qspecl_then [`e'`, `cfg`] impl_subgoal_tac) \\ fs[]
       \\ qexists_tac `fpOpt` \\ fs[semState_comp_eq, fpState_component_equality])
      \\ rpt strip_tac
      \\ qpat_x_assum `! st1 st2 env exps r. is_rewriteFPexl_list_correct rws _ _ _ _ _` (fn thm => rpt (first_x_assum (fn ithm => mp_then Any assume_tac ithm thm)))
      \\ first_x_assum (qspecl_then [`cfg`, `e'`] impl_subgoal_tac) \\ fs[]
      \\ first_x_assum (fn ithm => first_x_assum (fn thm => mp_then Any assume_tac ithm thm ))
      \\ first_x_assum (qspecl_then [`cfg`, `l`] impl_subgoal_tac) \\ fs[]
      \\ first_x_assum (mp_then Any (fn thm => thm |> Q.SPEC `fpOpt'` |> assume_tac) (CONJUNCT1 optUntil_evaluate_ok))
      \\ fs[]
      \\ qexists_tac `optUntil (q.fp_state.choices - st.fp_state.choices) fpOpt fpOpt'`
      \\ fs[semState_comp_eq, fpState_component_equality])
    \\ Cases_on `cfg.canOpt` \\ fs[]
    \\ (* by assumption *) cheat)
  (* Con *)
  >- (cheat)
  (* Var *)
  >- (cheat)
  (* Fun *)
  >- (cheat)
  (* App *)
  >- (cheat)
  (* Log *)
  >- (cheat)
  (* If *)
  >- (cheat)
  (* Mat *)
  >- (cheat)
  (* Let *)
  >- (cheat)
  (* Letrec *)
  >- (cheat)
  (* Tannot *)
  >- (cheat)
  (* Lannot *)
  >- (cheat)
  (* FpOptimise *)
  >- (cheat)
  (* eval_match empty *)
  >- (cheat)
  (* eval-match list *)
  \\ cheat
QED
end

Theorem compile_exp_correct:
  ! st1 env c e st2 res.
    evaluate st1 env (compile_exps c e) = (st2, Rval res) ==>
    ? (fp_opts:num -> rewrite_app list) g.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ c.optimisations;
                   opts := fp_opts |>)
               env e =
        (st2 with fp_state := st2.fp_state with
          <| rws := st2.fp_state.rws ++ c.optimisations; opts := g |>,
        Rval res)
Proof
  rw[compile_exps_def, no_optimisations_def, optimise_def]
  \\ imp_res_tac (CONJUNCT1 (prep evaluate_fp_rws_append))
  \\ cheat
  (* \\ first_x_assum (qspec_then `c.rws` assume_tac)
  \\ fs[] \\ qexists_tac `fpOpt` \\ qexists_tac `fpOpt2`
  \\ fs[semState_comp_eq, fpState_component_equality] *)
QED

Theorem REVERSE_no_optimisations:
  REVERSE (MAP (\e. no_optimisations cfg e) exps) =
  MAP (no_optimisations cfg) (REVERSE exps)
Proof
  Induct_on `exps` \\ fs[]
QED

local
  val eval_goal =
    ``\ (st1: 'ffi semanticPrimitives$state) env exps.
      ! cfg st2 r expsN.
        exps = (MAP (no_optimisations cfg) expsN) /\
        evaluate st1 env exps = (st2, r) /\
        ~st1.fp_state.canOpt ==>
        (! fpS.
        ~fpS.canOpt ==>
        evaluate (st1 with fp_state := fpS) env exps =
          (st2 with fp_state := fpS, r))``
  val eval_match_goal =
    ``\ (st1: 'ffi semanticPrimitives$state) env v pl err_v.
      ! cfg st2 r plN.
        pl = (MAP (\ (p,e). (p, no_optimisations cfg e)) plN) /\
        evaluate_match st1 env v pl err_v = (st2, r) /\
        ~ st1.fp_state.canOpt ==>
        (! fpS.
        ~ fpS.canOpt ==>
        evaluate_match (st1 with fp_state := fpS) env v pl err_v =
        (st2 with fp_state := fpS, r))``
  val expsN_cases_tac =
    Cases_on `expsN` \\ fs[] \\ Cases_on `t` \\ fs[];
  val evaluate_step =
    ntac 2 (TOP_CASE_TAC \\ fs[]);
  val single_step_tac =
    rpt strip_tac \\ rveq \\ fs[]
    \\ first_x_assum (fn thm => mp_tac (join_hyps thm))
    \\ fs[no_optimisations_def, evaluate_def, REVERSE_no_optimisations];
in
Theorem no_optimisations_empty_state:
  (! st1 env exps.
    ^eval_goal st1 env exps) /\
  (! st1 env v pl err_v.
    ^eval_match_goal st1 env v pl err_v)
Proof
  match_mp_tac (terminationTheory.evaluate_ind |> ISPEC eval_goal |> SPEC eval_match_goal)
  \\ rpt strip_tac \\ simp[evaluate_def] \\ rpt gen_tac \\ fs[PULL_EXISTS]
  (* e1 :: e2 :: es *)
  >- (
    expsN_cases_tac \\ reverse evaluate_step
    >- single_step_tac
    \\ reverse evaluate_step
    \\ single_step_tac
    \\ (rename1 `evaluate st2 env (no_optimisations cfg e2 :: MAP (no_optimisations cfg) exps) = (st3, Rval r)`
        ORELSE
       rename1 `evaluate st2 env (no_optimisations cfg e2 :: MAP (no_optimisations cfg) exps) = (st3, Rerr e)`)
    \\ first_x_assum (qspecl_then [`cfg`, `e2::exps`] impl_subgoal_tac)
    \\ fs[evaluate_def, no_optimisations_def] \\ cheat)
  (* Lit l *)
  >- (
    expsN_cases_tac \\ Cases_on `h` \\ fs[no_optimisations_def]
    \\ rpt strip_tac \\ fs[evaluate_def])
  (* Raise e *)
  >- (
    expsN_cases_tac \\ Cases_on `h` \\ fs[no_optimisations_def]
    \\ reverse evaluate_step
    \\ single_step_tac)
  (* Handle e pes *)
  >- (
    expsN_cases_tac \\ Cases_on `h` \\ fs[no_optimisations_def]
    \\ evaluate_step
    >- single_step_tac
    \\ reverse TOP_CASE_TAC \\ fs[]
    \\ single_step_tac
    \\ reverse TOP_CASE_TAC \\ fs[]
    \\ first_x_assum (qspecl_then [`cfg`, `l`] impl_subgoal_tac)
    \\ fs[evaluate_def] \\ cheat)
  (* Con cn es *)
  >- (
    cheat)
  (* nsLookup *)
  >- (
    expsN_cases_tac \\ Cases_on `h` \\ fs[no_optimisations_def]
    \\ rpt strip_tac \\ rveq \\ fs[evaluate_def]
    \\ TOP_CASE_TAC \\ fs[])
  (* Function definition *)
  >- (
    expsN_cases_tac \\ Cases_on `h` \\ fs[no_optimisations_def]
    \\ rpt strip_tac \\ rveq \\ fs[evaluate_def])
  (* App *)
  >- (
    expsN_cases_tac \\ Cases_on `h` \\ fs[no_optimisations_def]
    \\ reverse evaluate_step
    >- (
      rpt strip_tac \\ rveq \\ fs[]
      \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
      \\ fs[REVERSE_no_optimisations, evaluate_def])
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      TOP_CASE_TAC \\ fs[]
      >- (
        rpt strip_tac \\ rveq \\ fs[]
        \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
        \\ fs[REVERSE_no_optimisations, evaluate_def])
      \\ evaluate_step
      \\ rpt strip_tac \\ rveq \\ fs[]
      \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
      \\ fs[REVERSE_no_optimisations, evaluate_def]
      \\ cheat (* do_opapp gives no_optimisations exp *))
  \\ TOP_CASE_TAC \\ fs[]
  >- (
    rpt strip_tac \\ rveq \\ fs[]
    \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
    \\ fs[REVERSE_no_optimisations, evaluate_def])
  \\ evaluate_step
  \\ `~q.fp_state.canOpt` by (cheat)
  \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ rpt strip_tac \\ rveq \\ fs[]
  \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
  \\ fs[REVERSE_no_optimisations, evaluate_def])
  (* log *)
  >-(
    cheat)
  (* If *)
  >-(
    cheat)
  (* Mat *)
  >- (
    cheat)
  (* Let *)
  >- (
    cheat)
  (* Letrec *)
  >- (
    cheat)
  (* Tannot *)
  >- (
    cheat)
  (* Lannot *)
  >- (
    cheat)
  (* FpOptimise *)
  >- (
    expsN_cases_tac \\ Cases_on `h` \\ fs[no_optimisations_def]
    \\ evaluate_step
    \\ single_step_tac
    \\ fs[state_component_equality, fpState_component_equality] \\ cheat)
  (* Mat p1::ps *)
  >- (
    cheat)
QED
end

Theorem compile_decs_cons:
  compile_decs conf (p1::ps) = (compile_decs conf [p1]) ++ (compile_decs conf ps)
Proof
  Cases_on `p1` \\ Cases_on `ps` \\ fs[compile_decs_def]
QED

Theorem compile_decs_id:
  compile_decs no_fp_opt_conf prog = prog
Proof
  completeInduct_on `dec1_size prog` \\ rpt strip_tac \\ rveq
  \\ Cases_on `prog` \\ fs[compile_decs_def, Once compile_decs_cons]
  \\ first_assum (qspec_then `dec1_size t` mp_tac)
  \\ rpt strip_tac \\ fs[astTheory.dec_size_def]
  \\ pop_assum kall_tac
  \\ Cases_on `h` \\ fs[compile_decs_def]
  >- (cheat)
  >- (cheat)
  \\ fs[astTheory.dec_size_def]
QED

Theorem compile_decs_preserving:
! (semSt: 'ffi semanticPrimitives$state) semEnv prog fp_conf.
  ~ semantics_prog semSt semEnv prog Fail ==>
  ~ semantics_prog semSt semEnv (compile_decs fp_conf prog) Fail
Proof
cheat
QED

(** UNUSED
Definition is_fp_stable_def:
  is_fp_stable e st1 st2 env r =
    (evaluate st1 env [e] = (st2, r) ==>
    ! (fpS:fpState).
      evaluate (st1 with fp_state := fpS) env [e] = (st2 with fp_state := fpS, r))
End

Inductive is_correct_closures:
  (! cfg vs.
    (! env s e.
      MEM (Closure env s e) vs ==>
      (? eOld. e = no_optimisations cfg eOld) /\ is_unoptimisable_env env.v cfg) /\
    (! env funs x e y.
      MEM (Recclosure env funs x) vs /\
      find_recfun x funs = SOME (y, e) ==>
      (? eOld. e = no_optimisations cfg eOld) /\ is_unoptimisable_env (build_rec_env funs env env.v) cfg) /\
    (! vl.
      MEM (Vectorv vl) vs ==>
      is_correct_closures_list cfg vl) /\
    (! v vl.
      MEM v vs /\
      v_to_list v = SOME vl ==>
      is_correct_closures_list cfg vl) ==>
  is_correct_closures_list cfg vs)
  /\
  (! cfg e. is_correct_closures (cfg:config) ((Rerr e):(v list, v) result))
  /\
  (! cfg vs. is_correct_closures_list cfg vs ==> is_correct_closures cfg ((Rval vs):(v list, v) result))
  /\
  (! env cfg.
    (! n env2 s e.
      nsLookup env n = SOME (Closure env2 s e) ==>
      (? eOld. e = no_optimisations cfg eOld) /\
      is_unoptimisable_env env2.v cfg) /\
    (! n env2 funs x y e.
      nsLookup env n = SOME (Recclosure env2 funs x) /\
      find_recfun x funs = SOME (y, e) ==>
      (? eOld. e = no_optimisations cfg eOld) /\
      is_unoptimisable_env (build_rec_env funs env2 env2.v) cfg) /\
    (! n vl.
      nsLookup env n = SOME (Vectorv vl) ==>
      is_correct_closures_list cfg vl) /\
    (! n v vl.
      nsLookup env n = SOME v /\
      v_to_list v = SOME vl ==>
      is_correct_closures_list cfg vl) ==>
    is_unoptimisable_env env cfg)
End

val is_unoptimisable_env_def =
  (CONJ_LIST 3 is_correct_closures_cases) |> tl |> tl |> hd;

val is_correct_closures_list_def =
  (CONJ_LIST 3 is_correct_closures_cases) |> hd;

Inductive is_unoptimisable_store:
  (! store cfg.
    (! l env2 s e.
      store_lookup l store = SOME (Refv (Closure env2 s e)) ==>
      (? eOld. e = no_optimisations cfg eOld) /\
      is_unoptimisable_env env2.v cfg) /\
    (! l env2 funs x y e.
      store_lookup l store = SOME (Refv (Recclosure env2 funs x)) /\
      find_recfun x funs = SOME (y, e) ==>
      (? eOld. e = no_optimisations cfg eOld) /\
      is_unoptimisable_env (build_rec_env funs env2 env2.v) cfg) /\
    (! l vl.
      store_lookup l store = SOME (Refv (Vectorv vl)) ==>
      is_correct_closures_list cfg vl) /\
    (! l v vl.
      store_lookup l store = SOME (Refv v) /\
      v_to_list v = SOME vl ==>
      is_correct_closures_list cfg vl) /\
    (! l vl.
      store_lookup l store = SOME (Varray vl) ==>
      is_correct_closures_list cfg vl) ==>
    is_unoptimisable_store store cfg)
End

Theorem nsLookup_nsBind_cases:
  nsLookup (nsBind x v env) y = SOME vr ==>
  ((y = Short x) /\ vr = v) \/
  (nsLookup env y = SOME vr)
Proof
  Cases_on `y` \\ fs[namespacePropsTheory.nsLookup_nsBind]
  \\ Cases_on `env` \\ fs[namespaceTheory.nsBind_def, namespaceTheory.nsLookup_def]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem do_opapp_unoptimisable_env:
  ! vl st r cfg.
  is_correct_closures cfg (Rval vl) /\
  do_opapp vl = SOME (st, r) ==>
  is_unoptimisable_env st.v cfg
Proof
  fs[Once is_correct_closures_cases]
  \\ rpt (gen_tac ORELSE (disch_then assume_tac))
  \\ simp[Once is_unoptimisable_env_def] \\ fs[]
  \\ qpat_x_assum `is_correct_closures_list _ _`
      (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_list_def] thm))
  \\ fs[semanticPrimitivesPropsTheory.do_opapp_cases]
  THENL [
    rename1 `vl = [Closure env3 x e; v2]`
    \\ first_assum (qspecl_then [`env3`, `x`, `e`] assume_tac),
    rename [`vl = [Recclosure env3 funs x; v2]`, `find_recfun x funs = SOME (y, e)`]
    \\ first_assum (qspecl_then [`env3`, `funs`, `x`, `e`, `y`] impl_subgoal_tac) \\ fs[] ]
  \\ rveq \\ fs[]
  \\ rpt conj_tac \\ rpt (gen_tac ORELSE (disch_then assume_tac))
  \\ qpat_x_assum `is_unoptimisable_env _ _` (fn thm => assume_tac (SIMP_RULE std_ss [Once is_unoptimisable_env_def] thm))
  \\ fs[]
  \\ first_x_assum (mp_then Any assume_tac nsLookup_nsBind_cases) \\ fs[]
  \\ TRY (
      rename1 `Closure env2 s e2` \\ rveq
      \\ first_x_assum (qspecl_then [`env2`, `s`, `e2`] impl_subgoal_tac)
      \\ simp[] \\ NO_TAC)
  \\ TRY (
      rename [`Recclosure env2 funs y`, `find_recfun y funs = SOME (z, e2)`]
      \\ rveq
      \\ first_x_assum (qspecl_then [`env2`, `funs`, `y`, `e2`, `z`] impl_subgoal_tac)
      \\ simp[] \\ NO_TAC)
  \\ res_tac \\ conj_tac \\ TRY asm_exists_tac \\ fs[]
QED

Theorem is_correct_closures_list_reverse[local]:
  is_correct_closures_list cfg vs = is_correct_closures_list cfg (REVERSE vs)
Proof
  Cases_on `vs` \\ fs[]
  \\ rpt strip_tac
  \\ fs[Once is_correct_closures_list_def]
  \\ EQ_TAC
  >- (rpt strip_tac
      \\ simp[Once is_correct_closures_list_def]
      \\ rpt conj_tac
      \\ rpt strip_tac \\ fs[] \\ res_tac \\ asm_exists_tac \\ fs[])
  \\ disch_then (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_list_def] thm))
  \\ rpt conj_tac
  \\ rpt strip_tac \\ fs[] \\ res_tac \\ asm_exists_tac \\ fs[]
QED

Theorem do_opapp_no_optimisation[local]:
  is_correct_closures cfg (Rval vl) /\
  do_opapp vl = SOME (st, e) ==>
  ? eOld. e = no_optimisations cfg eOld
Proof
  fs[semanticPrimitivesPropsTheory.do_opapp_cases]
  \\ rpt strip_tac \\ fs[Once is_correct_closures_cases, Once is_correct_closures_list_def]
QED

Theorem is_correct_closures_Boolv[local]:
  is_correct_closures cfg (Rval [Boolv b])
Proof
  Cases_on `b`
  \\ fs[Boolv_def, Once is_correct_closures_cases, Once is_correct_closures_list_def, v_to_list_def]
QED

Theorem is_correct_closures_list_MEM:
  is_correct_closures_list cfg vl /\
  n < LENGTH vl ==>
  is_correct_closures cfg ((Rval [EL n vl]):(v list, v) result)
Proof
  simp[Once is_correct_closures_list_def]
  \\ rpt strip_tac
  \\ simp[Once is_correct_closures_cases, Once is_correct_closures_list_def]
  \\ imp_res_tac EL_MEM
  \\ rpt conj_tac \\ rpt strip_tac
  \\ TRY (qpat_x_assum `_ = EL _ _` (fn thm => fs[GSYM thm]))
  \\ res_tac \\ TRY (asm_exists_tac) \\ fs[]
QED

Theorem store_lookup_eq[local]:
  ! l1 l2 v1 v2 refs.
    (store_lookup l1 (LUPDATE v1 l2 refs) = SOME v2) ==>
    (l1 = l2 ==> v1 = v2) /\
    (l1 <> l2 ==> store_lookup l1 refs = SOME v2)
Proof
  Induct_on `l2` \\ fs[]
  \\ Cases_on `refs` \\ fs[LUPDATE_def, store_lookup_def]
  >- (rpt strip_tac \\ Cases_on `l1` \\ fs[])
  \\ rpt strip_tac
  \\ Cases_on `l1` \\ fs[]
QED

Theorem store_assign_Refv_unoptimisable[local]:
  is_unoptimisable_store refs cfg /\
  is_correct_closures_list cfg [h] /\
  store_assign lnum (Refv h) refs = SOME refs2 ==>
  is_unoptimisable_store refs2 cfg
Proof
  fs[store_assign_def] \\ rpt strip_tac \\ rveq
  \\ fs[is_unoptimisable_store_cases] \\ rpt strip_tac \\ fs[LUPDATE_def]
  \\ imp_res_tac store_lookup_eq
  \\ Cases_on `l = lnum` \\ fs[] \\ rveq
  \\ TRY (res_tac \\ asm_exists_tac \\ fs[])
  \\ TRY (qpat_x_assum `is_correct_closures_list _ _`
        (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_list_def] thm))
      \\ fs[]
      \\ qexists_tac `eOld` \\ fs[])
QED

Theorem store_assign_W8array_unoptimisable[local]:
  is_unoptimisable_store refs cfg /\
  store_assign lnum (W8array w) refs = SOME refs2 ==>
  is_unoptimisable_store refs2 cfg
Proof
  fs[store_assign_def] \\ rpt strip_tac \\ rveq
  \\ fs[is_unoptimisable_store_cases] \\ rpt strip_tac \\ fs[LUPDATE_def]
  \\ imp_res_tac store_lookup_eq
  \\ Cases_on `l = lnum` \\ fs[] \\ rveq
  \\ res_tac \\ asm_exists_tac \\ fs[]
QED

Theorem store_lookup_append[local]:
  store_lookup l (refs1 ++ refs2) = SOME v ==>
  (l < LENGTH refs1 /\ store_lookup l refs1 = SOME v) \/
  (l >= LENGTH refs1 /\ store_lookup (l - (LENGTH refs1)) refs2 = SOME v)
Proof
  fs[store_lookup_def] \\ rpt strip_tac
  \\ rveq \\ fs[]
  \\ Cases_on `l < LENGTH refs1` \\ fs[EL_APPEND1, EL_APPEND2]
QED

Theorem store_lookup_singleton[local]:
  store_lookup l1 [v] = SOME v2 ==>
  v = v2
Proof
  Cases_on `l1` \\ fs[store_lookup_def]
QED

Theorem store_alloc_Refv_unoptimisable[local]:
  is_unoptimisable_store refs cfg /\
  is_correct_closures_list cfg [h] /\
  store_alloc (Refv h) refs = (refs2, n) ==>
  is_unoptimisable_store refs2 cfg
Proof
  fs[store_alloc_def] \\ rpt strip_tac \\ rveq \\ fs[]
  \\ fs[is_unoptimisable_store_cases] \\ rpt conj_tac \\ fs[]
  \\ rpt strip_tac \\ fs[]
  \\ imp_res_tac store_lookup_append \\ fs[]
  \\ TRY (res_tac \\ asm_exists_tac \\ fs[])
  \\ TRY (qpat_x_assum `is_correct_closures_list _ _`
        (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_list_def] thm))
      \\ imp_res_tac store_lookup_singleton \\ fs[] \\ rveq
      \\ fs[]
      \\ qexists_tac `eOld` \\ fs[])
QED

Theorem store_alloc_W8array_unoptimisable[local]:
  is_unoptimisable_store refs cfg /\
  store_alloc (W8array w) refs = (refs2, n) ==>
  is_unoptimisable_store refs2 cfg
Proof
  fs[store_alloc_def] \\ rpt strip_tac \\ rveq \\ fs[]
  \\ fs[is_unoptimisable_store_cases] \\ rpt conj_tac \\ fs[]
  \\ rpt strip_tac \\ fs[]
  \\ imp_res_tac store_lookup_append \\ fs[]
  \\ TRY (res_tac \\ asm_exists_tac \\ fs[])
  \\ imp_res_tac store_lookup_singleton \\ fs[] \\ rveq
QED

Theorem v_to_list_list_to_v[local]:
  v_to_list (list_to_v v) = SOME v
Proof
  Induct_on `v` \\ fs[list_to_v_def, v_to_list_def]
QED

Theorem is_correct_closures_list_string[local]:
  is_correct_closures_list cfg (MAP (\c. Litv (Char c)) t)
Proof
  Induct_on `t` \\ fs[Once is_correct_closures_list_def]
  \\ rpt conj_tac \\ rpt strip_tac \\ res_tac
  \\ TRY (asm_exists_tac \\ fs[])
  \\ rveq \\ fs[v_to_list_def]
QED

Theorem is_correct_closures_list_append[local]:
  (is_correct_closures_list cfg xs /\
  is_correct_closures_list cfg ys) <=>
  is_correct_closures_list cfg (xs ++ ys)
Proof
  simp[Once is_correct_closures_cases]
  \\ EQ_TAC
  >- (rpt strip_tac
      \\ qpat_x_assum `is_correct_closures_list cfg ys`
          (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_cases, v_to_list_def] thm))
      \\ simp[Once is_correct_closures_cases, v_to_list_def]
      \\ rpt conj_tac \\ rpt strip_tac
      \\ res_tac \\ asm_exists_tac \\ fs[])
  \\ disch_then (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_cases, v_to_list_def] thm))
  \\ fs[]
  \\ rpt strip_tac
  \\ TRY (res_tac \\ asm_exists_tac \\ fs[])
  \\ Cases_on `ys` \\ fs[]
  \\ simp[Once is_correct_closures_cases]
  \\ rpt strip_tac
  \\ res_tac \\ asm_exists_tac \\ fs[]
QED

Theorem do_app_has_correct_closures[local]:
  is_correct_closures cfg (Rval vl) /\
  is_unoptimisable_store refs cfg /\
  do_app (refs, ffi) op (REVERSE vl) = SOME ((refs2, ffi2), r) ==>
  is_correct_closures cfg (list_result r) /\
  is_unoptimisable_store refs2 cfg
Proof
  reverse (Cases_on `r`) \\ fs[list_result_def, Once is_correct_closures_cases, Once is_correct_closures_list_def]
  \\ rpt (gen_tac ORELSE disch_then assume_tac) \\ fs[]
  \\ qpat_x_assum `do_app _ _ _ = SOME _` mp_tac
  >- (fs[semanticPrimitivesPropsTheory.do_app_cases] \\ rpt strip_tac \\ fs[Once is_correct_closures_cases]
      \\ TRY (Cases_on `uop` \\ fs[] \\ rveq \\ simp[Once is_correct_closures_cases, Once is_correct_closures_list_def] \\ NO_TAC)
      \\ TRY (pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[])
          \\ rpt strip_tac \\ rveq
          \\ fs[Once is_correct_closures_cases, Once is_correct_closures_list_def] \\ NO_TAC))
  \\ simp[semanticPrimitivesPropsTheory.do_app_cases]
  \\ rpt (gen_tac ORELSE disch_then assume_tac) \\ fs[] \\ rveq \\ fs[]
  \\ Cases_on `vl` \\ fs[] \\ rveq
  \\ TRY (ntac 2 (simp[Once is_correct_closures_cases, is_correct_closures_Boolv, v_to_list_def]) \\ NO_TAC)
  \\ TRY (Cases_on `uop` \\ fs[] \\ rveq \\ simp[Once is_correct_closures_cases, Once is_correct_closures_list_def, v_to_list_def] \\ NO_TAC)
  >- (imp_res_tac store_assign_Refv_unoptimisable
      \\ conj_tac >- (ntac 2 (simp[Once is_correct_closures_cases, v_to_list_def]))
      \\ first_x_assum irule \\ fs[]
      \\ simp[Once is_correct_closures_list_def] \\ conj_tac \\ metis_tac[])
  >- (imp_res_tac store_alloc_Refv_unoptimisable
      \\ conj_tac >- (ntac 2 (simp[Once is_correct_closures_cases, v_to_list_def]))
      \\ first_x_assum irule \\ fs[]
      \\ simp[Once is_correct_closures_list_def] \\ conj_tac \\ metis_tac[])
  >- (rename1 `store_lookup x refs = SOME (Refv v)`
      \\ Cases_on `v` \\ simp[Once is_correct_closures_cases, Once is_correct_closures_list_def]
      \\ fs[v_to_list_def]
      \\ fs[is_unoptimisable_store_cases] \\ rpt strip_tac
      \\ res_tac \\ fs[] \\ TRY (qexists_tac `eOld` \\ fs[]))
  >- (imp_res_tac store_alloc_W8array_unoptimisable
      \\ conj_tac >- (ntac 2 (simp[Once is_correct_closures_cases, v_to_list_def]))
      \\ fs[])
  >- (imp_res_tac store_assign_W8array_unoptimisable
      \\ conj_tac >- (ntac 2 (simp[Once is_correct_closures_cases, v_to_list_def]))
      \\ first_x_assum irule \\ fs[]
      \\ simp[Once is_correct_closures_list_def] \\ conj_tac \\ metis_tac[])
  >- (imp_res_tac store_assign_W8array_unoptimisable
      \\ conj_tac >- (ntac 2 (simp[Once is_correct_closures_cases, v_to_list_def]))
      \\ first_x_assum irule \\ fs[]
      \\ simp[Once is_correct_closures_list_def] \\ conj_tac \\ metis_tac[])
  >- (imp_res_tac store_assign_W8array_unoptimisable
      \\ conj_tac >- (ntac 2 (simp[Once is_correct_closures_cases, v_to_list_def]))
      \\ first_x_assum irule \\ fs[]
      \\ simp[Once is_correct_closures_list_def] \\ conj_tac \\ metis_tac[])
  >- (Cases_on `str`  \\ fs[list_to_v_def]
      >- (ntac 2 (fs[Once is_correct_closures_cases, Once is_correct_closures_list_def, v_to_list_def]))
      \\ fs[Once is_correct_closures_cases, Once is_correct_closures_list_def, v_to_list_def]
      \\ rpt gen_tac \\ TOP_CASE_TAC \\ fs[v_to_list_list_to_v] \\ rveq
      \\ rpt strip_tac \\ rveq
      \\ `Litv (Char h)::MAP (\c. Litv (Char c)) (EXPLODE t) =
          MAP (\c. Litv (Char c)) (h::EXPLODE t)` by (EVAL_TAC)
      \\ pop_assum (fn thm => once_rewrite_tac[thm])
      \\ fs[is_correct_closures_list_string])
  >- (rename1 `~ (Num (ABS index) >= LENGTH vs)`
          \\ `Num (ABS index) < LENGTH vs` by (fs[])
          \\ imp_res_tac EL_MEM
          \\ ntac 2 (simp [Once is_correct_closures_cases]) \\ rpt conj_tac \\ rpt strip_tac
          \\ TRY (qpat_x_assum `_ = EL _ _` (fn thm => fs[GSYM thm]))
          \\ qpat_x_assum `is_correct_closures_list _ _` (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_cases] thm))
          \\ fs[] \\ res_tac
          \\ asm_exists_tac \\ fs[])
  >- ( (* Same alloc lemma for store varray *) cheat)
  >- ( (* same alloc ... *) cheat)
  >- (qpat_x_assum `is_unoptimisable_store _ _`
      (fn thm => assume_tac (SIMP_RULE std_ss [is_unoptimisable_store_cases] thm))
      \\ fs[] \\ res_tac
      \\ irule is_correct_closures_list_MEM \\ fs[])
  >- ( (* also requires side lemma on storing... *) cheat)
  >- (simp[Once is_correct_closures_cases, Once is_correct_closures_list_def, v_to_list_def]
      \\ rpt conj_tac \\ rpt strip_tac
      >- (Cases_on `xs` \\ Cases_on `ys` \\ fs[list_to_v_def])
      >- (Cases_on `xs` \\ Cases_on `ys` \\ fs[list_to_v_def])
      >- (Cases_on `xs` \\ Cases_on `ys` \\ fs[list_to_v_def])
      >- (Cases_on `xs` \\ Cases_on `ys` \\ fs[list_to_v_def])
      >- (Cases_on `xs` \\ Cases_on `ys` \\ fs[list_to_v_def])
      \\ fs[v_to_list_list_to_v] \\ rveq
      \\ once_rewrite_tac [GSYM is_correct_closures_list_append]
      \\ conj_tac \\ first_x_assum irule \\ asm_exists_tac  \\ fs[])
  >- (pop_assum mp_tac
      \\ rpt (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ rveq \\ fs[]
      >- (ntac 2 (fs[Once is_correct_closures_cases, v_to_list_def]))
      \\ irule store_assign_W8array_unoptimisable \\ asm_exists_tac \\ fs[])
QED

Definition eq_upto_sc_def:
  eq_upto_sc [] [] = T /\
  eq_upto_sc [App op1 es1] [e2] =
    (if (isFpOp op1) then
      (e2 = FpOptimise NoOpt (App op1 es1) \/
      e2 = App op1 es1)
    else e2 = App op1 es1) /\
  eq_upto_sc [e1] [e2] = (e1 = e2) /\
  eq_upto_sc (e1::es1) (e2::es2) =
    (eq_upto_sc [e1] [e2] /\
    eq_upto_sc es1 es2) /\
  eq_upto_sc _ _ = F
End

Theorem eq_upto_sc_sing:
  eq_upto_sc [e1] exps ==>
  ? e2. exps = [e2]
Proof
  Cases_on `exps` \\ fs[eq_upto_sc_def]
  \\ Cases_on `t` \\ fs[eq_upto_sc_def]
QED

Theorem eq_upto_sc_refl:
  eq_upto_sc exps1 exps1
Proof
  Induct_on `exps1` \\ fs[eq_upto_sc_def]
  \\ rpt strip_tac \\ Cases_on `h` \\ Cases_on `exps1` \\ fs[eq_upto_sc_def]
QED

Theorem no_optimisations_Raise:
  Raise e1 = no_optimisations cfg e2 ==>
  ? eOld. e1 = no_optimisations cfg eOld
Proof
  measureInduct_on `exp_size e2`
  \\ Cases_on `e2` \\ fs[no_optimisations_def]
  \\ rpt strip_tac
  >- (qexists_tac `e` \\ fs[])
  >- (Cases_on `o'` \\ fs[astTheory.isFpOp_def])
  \\ first_x_assum (qspec_then `e` impl_subgoal_tac)
  \\ TRY (asm_exists_tac)
  \\ fs[astTheory.exp_size_def]
QED

local
  val eval_goal =
    ``\ (st1: 'ffi semanticPrimitives$state) env exps.
      ! cfg st2 r expsN.
        evaluate st1 env exps = (st2, r) /\
        is_unoptimisable_env (env.v) cfg /\
        is_unoptimisable_store (st1.refs) cfg /\
        eq_upto_sc exps (MAP (no_optimisations cfg) expsN) ==>
        (! fpS.
        evaluate (st1 with fp_state := fpS) env exps =
          (st2 with fp_state := fpS, r)) /\
        is_correct_closures cfg r /\
        is_unoptimisable_store (st2.refs) cfg``
  val eval_match_goal =
    ``\ (st1: 'ffi semanticPrimitives$state) env v pl err_v.
      ! cfg st2 r plN.
        evaluate_match st1 env v pl err_v = (st2, r) /\
        is_unoptimisable_env (env.v) cfg /\
        is_unoptimisable_store (st1.refs) cfg /\
        pl = MAP (\ (p, e). (p, no_optimisations cfg e)) plN ==>
        (! fpS.
        evaluate_match (st1 with fp_state := fpS) env v pl err_v =
        (st2 with fp_state := fpS, r)) /\
        is_correct_closures cfg r /\
        is_unoptimisable_store st2.refs cfg``
  val isFpOp_tac = rename1 `isFpOp op` \\ Cases_on `isFpOp op` \\ fs[eq_upto_sc_def];
  val eq_upto_sc_case_tac =
    imp_res_tac eq_upto_sc_sing \\ Cases_on `expsN` \\ fs[] \\ rveq
    \\ Cases_on `h` \\ fs[no_optimisations_def, eq_upto_sc_def] \\ rveq
    \\ TRY isFpOp_tac;
in
Theorem no_optimisations_is_fp_stable:
  (! st1 env exps.
    ^eval_goal st1 env exps) /\
  (! st1 env v pl err_v.
    ^eval_match_goal st1 env v pl err_v)
Proof
  mp_tac (terminationTheory.evaluate_ind |> ISPEC eval_goal |> SPEC eval_match_goal)
  \\ impl_tac \\ fs[] \\ rpt gen_tac \\ rpt conj_tac \\ rpt gen_tac
  \\ rpt (disch_then assume_tac) \\ rpt gen_tac \\ rpt (disch_then assume_tac) \\ fs[]
  \\ TRY (qpat_x_assum `evaluate _ _ _ = _` mp_tac) \\ simp[evaluate_def]
  >- (ntac 2 (fs[Once is_correct_closures_cases]))
  (* e1 :: e2 :: es *)
  >- (
    Cases_on `expsN` \\ fs[no_optimisations_def, eq_upto_sc_def]
   \\ Cases_on `t` \\ fs[no_optimisations_def, eq_upto_sc_def]
    \\ rveq
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    >- (rpt strip_tac \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `[h]`] impl_subgoal_tac)
        \\ fs[eq_upto_sc_def])
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ last_x_assum (qspecl_then [`cfg`, `[h]`] impl_subgoal_tac) \\ fs[eq_upto_sc_def]
    \\ first_x_assum (qspecl_then [`cfg`, `h'::t'`] impl_subgoal_tac) \\ fs[eq_upto_sc_def]
    \\ rpt strip_tac \\ rveq
    \\ rpt strip_tac \\ imp_res_tac evaluate_sing \\ rveq
    \\ fs[Once is_correct_closures_cases]
    \\ rename1 `is_correct_closures_list cfg (v1::vs)`
    \\ `v1 :: vs = [v1]++vs` by EVAL_TAC
    \\ pop_assum (fn thm => once_rewrite_tac[thm])
    \\ once_rewrite_tac[GSYM is_correct_closures_list_append] \\ fs[])
  (* values *)
  >- (
    Cases_on `expsN` \\ fs[no_optimisations_def, eq_upto_sc_def] \\ rveq
    \\ Cases_on `t` \\ fs[no_optimisations_def, eq_upto_sc_def] \\ rveq
    \\ rw[evaluate_def]
    \\ fs[Once is_correct_closures_cases, Once is_correct_closures_list_def, v_to_list_def])
  (* Raise e *)
  >- (
    imp_res_tac eq_upto_sc_sing \\ Cases_on `expsN` \\ fs[eq_upto_sc_def] \\ rveq
    \\ Cases_on `h` \\ fs[no_optimisations_def, eq_upto_sc_def] \\ rveq
    \\ TRY isFpOp_tac
    \\ Cases_on `e'` \\ fs[no_optimisations_def]
    \\ TRY isFpOp_tac
    \\ ntac 2 (TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ rpt (disch_then assume_tac) \\ fs[] \\ rveq
    \\ first_x_assum (qspecl_then [`cfg`, `[e']`] impl_subgoal_tac)
    \\ fs[eq_upto_sc_refl]
    \\ rpt strip_tac
    \\ fs[evaluate_def, Once is_correct_closures_cases, Once is_correct_closures_list_def])
  (* Handle *)
  >- (
    eq_upto_sc_case_tac
    \\ ntac 2 (TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ TRY (TOP_CASE_TAC \\ fs[])
    \\ rpt gen_tac \\ rpt (disch_then assume_tac) \\ fs[] \\ rveq
    \\ first_x_assum (qspecl_then [`cfg`, `[e']`] impl_subgoal_tac)
    \\ fs[evaluate_def, eq_upto_sc_refl]
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`l`] mp_tac) \\ fs[])
  (* Constructor *)
  >- (
    eq_upto_sc_case_tac
    \\ reverse TOP_CASE_TAC \\ fs[evaluate_def]
    >- (rpt strip_tac \\ rveq \\ fs[Once is_correct_closures_cases, Once is_correct_closures_list_def])
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    >- (rpt strip_tac \\ rveq
        \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] mp_tac)
        \\ fs[REVERSE_no_optimisations, eq_upto_sc_refl])
    \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
    \\ fs[REVERSE_no_optimisations, eq_upto_sc_refl]
    \\ TOP_CASE_TAC \\ rpt strip_tac \\ rveq \\ fs[]
    \\ rpt strip_tac \\ rveq
    >- (fs[Once is_correct_closures_cases, Once is_correct_closures_list_def])
    \\ qpat_x_assum `build_conv _ _ _ = SOME _` mp_tac \\ fs[build_conv_def]
    \\ TOP_CASE_TAC
    >- (rpt strip_tac \\ rveq \\ fs[Once is_correct_closures_cases, Once is_correct_closures_list_def, v_to_list_def])
    \\ rpt (TOP_CASE_TAC \\ fs[]) \\ strip_tac \\ rveq
    \\ simp[Once is_correct_closures_cases, Once is_correct_closures_list_def]
    \\ Cases_on `REVERSE a` \\ fs[v_to_list_def]
    >- (rpt strip_tac \\ rveq
        \\ fs[Once is_correct_closures_cases, Once is_correct_closures_list_def])
    \\ rpt strip_tac \\ rveq \\ Cases_on `t` \\ fs[v_to_list_def]
    \\ rename1 `v_to_list (Conv (SOME r) (h1::h2::hs)) = SOME _`
    \\ Cases_on `hs` \\ fs[v_to_list_def]
    \\ pop_assum mp_tac \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ fs[] \\ rveq
    \\ Cases_on `a` \\ fs[] \\ rveq
    \\ `h1 :: x = [h1] ++ x` by fs[]
    \\ pop_assum (fn thm => once_rewrite_tac[thm])
    \\ once_rewrite_tac [GSYM is_correct_closures_list_append]
    \\ qpat_x_assum `is_correct_closures _ _` (fn thm =>
        assume_tac (SIMP_RULE std_ss [Once is_correct_closures_cases] thm))
    \\ fs[]
    \\ `[h;h1] = [h] ++ [h1]` by (fs[])
    \\ pop_assum (fn thm => qpat_x_assum `is_correct_closures_list _ _` (fn thm2 => assume_tac (REWRITE_RULE [thm, GSYM is_correct_closures_list_append] thm2)))
    \\ fs[Once is_correct_closures_list_def])
  (* variable lookup *)
  >- (
    eq_upto_sc_case_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ rw[evaluate_def]
    \\ fs[Once is_correct_closures_cases]
    \\ Cases_on `x` \\ simp[Once is_correct_closures_list_def, v_to_list_def]
    \\ TRY (res_tac \\ TRY asm_exists_tac \\ fs[])
    \\ qexists_tac `eOld` \\ fs[])
  (* Function definition *)
  >- (
    eq_upto_sc_case_tac
    \\ rw[evaluate_def] \\ fs[Once is_correct_closures_cases]
    \\ simp[Once is_correct_closures_list_def] \\ fs[v_to_list_def] \\ conj_tac
    >- (qexists_tac `e'` \\ fs[])
    \\ simp [Once is_unoptimisable_env_def]
    \\ rpt strip_tac \\ res_tac \\ TRY asm_exists_tac \\ fs[])
  (* App *)
  >- (
    imp_res_tac eq_upto_sc_sing \\ fs[] \\ rveq \\ fs[]
    \\ Cases_on `x0` \\ TRY (fs[no_optimisations_def, eq_upto_sc_def] \\ NO_TAC)
    \\ fs[eq_upto_sc_def]
    \\ Cases_on `x0` \\ fs[eq_upto_sc_def, no_optimisations_def]
    \\ rename1 `eq_upto_sc [if (isFpOp op2) then _ else _] [App op1 es]`
    \\ Cases_on `isFpOp op2` \\ fs[eq_upto_sc_def] \\ rveq
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ TRY
        (rpt strip_tac \\ rveq
        \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] mp_tac)
        \\ fs[REVERSE_no_optimisations, evaluate_def, eq_upto_sc_refl] \\ NO_TAC)
    \\ TOP_CASE_TAC \\ fs[] \\ TRY (fs[astTheory.isFpOp_def]\\ NO_TAC)
    (* Opapp case *)
    \\ TRY (
        rename1 `op = Opapp` \\ rveq
        \\ TOP_CASE_TAC \\ fs[]
        >- (rpt strip_tac \\ rveq \\ fs[evaluate_def]
            \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
            \\ fs[REVERSE_no_optimisations]
            \\ fs[Once is_correct_closures_cases, eq_upto_sc_refl])
        \\ PairCases_on `x` \\ fs[]
        \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
        \\ fs[REVERSE_no_optimisations, eq_upto_sc_refl]
        \\ qpat_x_assum `is_correct_closures _ _` (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_cases] thm))
        \\ fs[Once is_correct_closures_list_reverse]
        \\ last_assum (mp_then Any assume_tac do_opapp_unoptimisable_env)
        \\ pop_assum (fn thm => imp_res_tac (SIMP_RULE std_ss [Once is_correct_closures_cases] thm))
        \\ last_assum (mp_then Any assume_tac do_opapp_no_optimisation)
        \\ pop_assum (fn thm => imp_res_tac (SIMP_RULE std_ss [Once is_correct_closures_cases] thm))
        \\ fs[] \\ rveq
        \\ TOP_CASE_TAC \\ fs[]
        \\ rpt (gen_tac ORELSE (disch_then assume_tac)) \\ fs[evaluate_def]
        \\ rveq
        >- (fs[Once is_correct_closures_cases])
        \\ first_x_assum (qspecl_then [`cfg`, `[eOld]`] impl_subgoal_tac)
        \\ fs[eq_upto_sc_refl, dec_clock_def] \\ NO_TAC)
    (* solve first bogus case for fp op *)
    \\ TRY (
      rename1 `evaluate st env (REVERSE es) = (st3, Rerr err)`
      \\ Cases_on `e` \\ fs[no_optimisations_def]
      \\ rename1 `(if (isFpOp op2) then _ else _) = _` \\ Cases_on `isFpOp op2` \\ fs[]
      \\ rveq \\ fs[] \\ NO_TAC)
    (* solve second bogus case for fp op *)
    \\ TRY (
      rename1 `no_optimisations cfg e = App op es` \\ rename1 `op <> Opapp`
      \\ Cases_on `e` \\ fs[no_optimisations_def]
      \\ rename1 `(if (isFpOp op2) then _ else _) = _` \\ Cases_on `isFpOp op2` \\ fs[]
      \\ rveq \\ fs[] \\ NO_TAC)
    (* get evaluations from IH *)
    \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
    \\ simp[REVERSE_no_optimisations, eq_upto_sc_refl]
    (* MARKER *)
    \\ TOP_CASE_TAC \\ fs[]
    >- (rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
        \\ fs[REVERSE_no_optimisations]
        \\ fs[Once is_correct_closures_cases])
    \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] impl_subgoal_tac)
    \\ fs[REVERSE_no_optimisations]
    \\ rpt (TOP_CASE_TAC \\ fs[]) \\ rpt (disch_then assume_tac) \\ fs[] \\ rveq
    \\ fs[evaluate_def, REVERSE_no_optimisations]
    \\ first_x_assum (mp_then Any assume_tac do_app_has_correct_closures)
    \\ first_x_assum (qspec_then `cfg` impl_subgoal_tac) \\ fs[])
  (* do_log *)
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TRY isFpOp_tac
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    >- (rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `e`] impl_subgoal_tac)
        \\ fs[])
    \\ TOP_CASE_TAC \\ fs[]
    >- (rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `e`] impl_subgoal_tac)
        >- fs[]
        \\ fs[Once is_correct_closures_cases])
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- (rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `e`] impl_subgoal_tac)
        >- fs[]
        \\ fs[Once is_correct_closures_cases]
        \\ qpat_x_assum `do_log _ _ _ = _` mp_tac
        \\ Cases_on `a` \\ fs[do_log_def]
        \\ TOP_CASE_TAC \\ fs[] \\ rpt strip_tac \\ fs[] \\ assume_tac (GEN_ALL (SIMP_RULE std_ss [Once is_correct_closures_cases] is_correct_closures_Boolv))
        \\ fs[])
    \\ disch_then assume_tac
    \\ rename1 `do_log l (HD vl) (no_optimisations cfg e0) = SOME (Exp e1)`
    \\ `e1 = no_optimisations cfg e0`
          by (qpat_x_assum `do_log _ _ _ = _` mp_tac
              \\ fs[do_log_def] \\ TOP_CASE_TAC \\ fs[])
    \\ rveq \\ fs[]
    \\ last_x_assum (qspecl_then [`cfg`, `e`] impl_subgoal_tac)
    \\ fs[]
    \\ last_x_assum (qspecl_then [`cfg`, `e0`] impl_subgoal_tac)
    \\ fs[evaluate_def])
  (* do_if *)
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TRY isFpOp_tac
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    >- (rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `e`] impl_subgoal_tac)
        \\ fs[])
    \\ TOP_CASE_TAC \\ fs[]
    >- (rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `e`] impl_subgoal_tac)
        >- fs[]
        \\ fs[Once is_correct_closures_cases])
    \\ disch_then assume_tac
    \\ rename1 `do_if (HD vl) (no_optimisations cfg e1) (no_optimisations cfg e2) = SOME e3`
    \\ last_x_assum (qspecl_then [`cfg`, `e`] impl_subgoal_tac)
    \\ fs[]
    \\ imp_res_tac do_if_cases \\ rveq
    THENL[
      last_x_assum (qspecl_then [`cfg`, `e1`] impl_subgoal_tac),
      last_x_assum (qspecl_then [`cfg`, `e2`] impl_subgoal_tac)]
    \\ fs[evaluate_def])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TRY isFpOp_tac
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[evaluate_def]
    \\ first_x_assum (qspecl_then [`cfg`, `e'`] impl_subgoal_tac) \\ fs[]
    \\ first_x_assum (qspecl_then [`cfg`, `l`] impl_subgoal_tac) \\ fs[])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TRY isFpOp_tac
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ rpt (disch_then assume_tac) \\ fs[] \\ rveq \\ fs[evaluate_def]
    \\ first_x_assum (qspecl_then [`cfg`, `e`] impl_subgoal_tac) \\ fs[]
    \\ first_x_assum (qspecl_then [`cfg`, `e0`] impl_subgoal_tac) \\ fs[]
    \\ rename1 `nsOptBind so (HD vl) env.v`
    \\ Cases_on `so` \\ fs[namespaceTheory.nsOptBind_def]
    \\ qpat_x_assum `is_correct_closures _ _` (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_cases] thm))
    \\ fs[]
    \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
    \\ fs[Once is_unoptimisable_env_def] \\ rpt strip_tac \\ imp_res_tac nsLookup_nsBind_cases
    \\ rveq  \\ fs[] \\ res_tac
    \\ qpat_x_assum `is_correct_closures_list cfg _` (fn thm => assume_tac (SIMP_RULE std_ss [Once is_correct_closures_cases] thm))
    \\ fs[] \\ TRY (qexists_tac `eOld`) \\ fs[])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TRY isFpOp_tac
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- (rpt strip_tac \\ rveq \\ fs[evaluate_def, Once is_correct_closures_cases])
    \\ disch_then assume_tac \\ fs[PULL_EXISTS]
    \\ first_x_assum (qspecl_then [`cfg`, `e'`] impl_subgoal_tac) \\ fs[evaluate_def]
    \\ ntac 3 (pop_assum kall_tac)  (* TODO: extract lemma *)
    \\ fs[Once is_unoptimisable_env_def] \\ rpt strip_tac
    \\ cheat)
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TRY isFpOp_tac
    \\ disch_then assume_tac \\ fs[PULL_EXISTS]
    \\ first_x_assum (qspecl_then [`cfg`, `e'`] impl_subgoal_tac) \\ fs[evaluate_def])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TRY isFpOp_tac
    \\ disch_then assume_tac \\ fs[PULL_EXISTS]
    \\ first_x_assum (qspecl_then [`cfg`, `e'`] impl_subgoal_tac) \\ fs[evaluate_def])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TRY isFpOp_tac
    (* isFpOp *)
    >- (
      simp[evaluate_def]
      \\ Cases_on `evaluate (st with fp_state := st.fp_state with canOpt := F) env (REVERSE (MAP (\a. no_optimisations cfg a) l))` \\ fs[]
      \\ reverse (Cases_on `r'`) \\ fs[]
      >- (
        disch_then assume_tac \\ fs[] \\ rveq
        \\ fs[state_component_equality, PULL_EXISTS]
        \\ rpt conj_tac \\ fs[Once is_correct_closures_rules]
        >-
        >- (fs[Once is_correct_closures_cases]
        >- (


    \\ disch_then assume_tac \\ fs[PULL_EXISTS]
    \\ first_x_assum (qspecl_then [`cfg`, `e'`] impl_subgoal_tac) \\ fs[evaluate_def])
  >- (cheat)
  >- (fs[evaluate_def] \\ rveq \\ fs[Once is_correct_closures_cases, Once is_correct_closures_list_def])
  >- (cheat)
QED
end

(* TODO: optimise_dec *)

(*
Theorem compile_correct:
  compile c prog = progN ==>
  let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
  ¬semantics_prog s env prog Fail ==>
  (* TODO: Side conditions???
   backend_config_ok c ∧ lab_to_targetProof$mc_conf_ok mc ∧ mc_init_ok c mc ∧
   installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names ffi (heap_regs c.stack_conf.reg_names) mc ms ⇒ *)
  ! x.
    x IN semantics_prog s env prog ==>
    ? fpOpt.
      x IN semantics_prog (s with fp_state := s.fp_state with <| rws := (c.rws); opts := fpOpt |>) env prog
Proof
  rw[compile_def, no_optimisations_def, optimise_def, primSemEnvTheory.prim_sem_env_eq]
  \\ Cases_on `x` \\ fs[]
  \\ fs[semantics_prog_def]
  \\ qexists_tac `no_fp_opts` \\ fs[]
  \\ cheat
QED
*)
 **)

val _ = export_theory ();