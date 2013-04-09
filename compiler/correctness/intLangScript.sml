open HolKernel bossLib boolLib boolSimps pairTheory listTheory rich_listTheory pred_setTheory finite_mapTheory relationTheory SatisfySimps arithmeticTheory quantHeuristicsLib lcsymtacs
open MiniMLTheory miscTheory miniMLExtraTheory compileTerminationTheory
val _ = new_theory "intLang"

(* Cevaluate functional equations *)

val Cevaluate_raise = store_thm(
"Cevaluate_raise",
``∀c s env err res. Cevaluate c s env (CRaise err) res = (res = (s, Rerr (Rraise err)))``,
rw[Once Cevaluate_cases])

val Cevaluate_lit = store_thm(
"Cevaluate_lit",
``∀c s env l res. Cevaluate c s env (CLit l) res = (res = (s, Rval (CLitv l)))``,
rw[Once Cevaluate_cases])

val Cevaluate_var = store_thm(
"Cevaluate_var",
``∀c s env vn res. Cevaluate c s env (CVar vn) res = (vn < LENGTH env ∧ (res = (s, Rval (EL vn env))))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_fun = store_thm(
"Cevaluate_fun",
``∀c s env b res. Cevaluate c s env (CFun b) res =
  (∀l. (b = INR l) ⇒ l ∈ FDOM c ∧ ((c ' l).nz = 1) ∧ ((c ' l).ez = LENGTH env)) ∧
  (res = (s, Rval (CRecClos env [b] 0)))``,
rw[Once Cevaluate_cases] >> metis_tac[])

val _ = export_rewrites["Cevaluate_raise","Cevaluate_lit","Cevaluate_var","Cevaluate_fun"]

val Cevaluate_con = store_thm(
"Cevaluate_con",
``∀c s env cn es res. Cevaluate c s env (CCon cn es) res =
(∃s' vs. Cevaluate_list c s env es (s', Rval vs) ∧ (res = (s', Rval (CConv cn vs)))) ∨
(∃s' err. Cevaluate_list c s env es (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_tageq = store_thm(
"Cevaluate_tageq",
``∀c s env exp n res. Cevaluate c s env (CTagEq exp n) res =
  (∃s' m vs. Cevaluate c s env exp (s', Rval (CConv m vs)) ∧ (res = (s', Rval (CLitv (Bool (n = m)))))) ∨
  (∃s' err. Cevaluate c s env exp (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_let = store_thm(
"Cevaluate_let",
``∀c s env e b res. Cevaluate c s env (CLet e b) res =
(∃s' v. Cevaluate c s env e (s', Rval v) ∧
     Cevaluate c s' (v::env) b res) ∨
(∃s' err. Cevaluate c s env e (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

val Cevaluate_proj = store_thm(
"Cevaluate_proj",
``∀c s env exp n res. Cevaluate c s env (CProj exp n) res =
  (∃s' m vs. Cevaluate c s env exp (s', Rval (CConv m vs)) ∧ (n < LENGTH vs) ∧ (res = (s', Rval (EL n vs)))) ∨
  (∃s' err. Cevaluate c s env exp (s', Rerr err) ∧ (res = (s', Rerr err)))``,
rw[Once Cevaluate_cases] >> PROVE_TAC[])

(* syneq equivalence relation lemmas *)

(* TODO: move *)
val syneq_rules = CompileTheory.syneq_rules
val syneq_cb_aux_def = CompileTheory.syneq_cb_aux_def
fun RATOR_ASSUM t ttac (g as (asl,w)) = UNDISCH_THEN (first (can (match_term t) o fst o strip_comb) asl) ttac g
fun rator_assum q ttac = Q_TAC (C RATOR_ASSUM ttac) q
fun RATOR_KEEP_ASSUM t ttac (g as (asl,w)) = ttac (ASSUME (first (can (match_term t) o fst o strip_comb) asl)) g
fun rator_k_assum q ttac = Q_TAC (C RATOR_KEEP_ASSUM ttac) q
val rev_assum_list = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC)
fun last_x_assum x = rev_assum_list >> first_x_assum x >> rev_assum_list

val find_index_ALL_DISTINCT_EL = store_thm(
"find_index_ALL_DISTINCT_EL",
``∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))``,
Induct >- rw[] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL])
val _ = export_rewrites["find_index_ALL_DISTINCT_EL"]

val find_index_LESS_LENGTH = store_thm(
"find_index_LESS_LENGTH",
``∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls)``,
Induct >> rw[find_index_def] >>
res_tac >>
srw_tac[ARITH_ss][arithmeticTheory.ADD1])

val syneq_refl = save_thm("syneq_refl", SIMP_RULE std_ss [] (CONJUNCT1 syneq_rules))
val _ = export_rewrites["syneq_refl"]

val syneq_exp_refl = List.nth(CONJUNCTS syneq_rules,5)
val syneq_cb_refl = List.nth(CONJUNCTS syneq_rules,22)

val equality_lambda = store_thm("equality_lambda",
  ``(λx y. x = y) = $=``,
  simp[FUN_EQ_THM])

val syneq_sym = store_thm("syneq_sym",
  ``(∀c1 c2 x y. syneq c1 c2 x y ⇒ syneq c2 c1 y x) ∧
    (∀c1 c2 ez1 ez2 V exp1 exp2. syneq_exp c1 c2 ez1 ez2 V exp1 exp2 ⇒ syneq_exp c2 c1 ez2 ez1 (inv V) exp2 exp1) ∧
    (∀c1 c2 ez1 ez2 V defs1 defs2. syneq_cb c1 c2 ez1 ez2 V defs1 defs2 ⇒ syneq_cb c2 c1 ez2 ez1 (inv V) defs2 defs1)``,
  ho_match_mp_tac syneq_ind >>
  strip_tac >- rw[Once syneq_cases] >>
  strip_tac >- rw[Once syneq_cases] >>
  strip_tac >- (
    rw[] >> simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    disj2_tac >>
    qexists_tac`inv V` >>
    simp[inv_DEF] >>
    PROVE_TAC[]) >>
  strip_tac >- rw[Once syneq_cases] >>
  strip_tac >- (
    rw[] >>
    rw[Once syneq_cases] >>
    disj1_tac >> simp[inv_DEF] ) >>
  strip_tac >- (
    rw[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,inv_DEF] >>
    pop_assum mp_tac >> simp[MEM_ZIP] >>
    PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    fs[optionTheory.OPTREL_def] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    disj2_tac >>
    pop_assum mp_tac >>
    qmatch_abbrev_tac`a ==> b` >>
    qsuff_tac`a = b` >- rw[] >>
    unabbrev_all_tac >>
    rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
    simp[FUN_EQ_THM,inv_DEF] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases,inv_DEF] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,inv_DEF] >>
    pop_assum mp_tac >> simp[MEM_ZIP] >>
    fsrw_tac[DNF_ss][] >>
    rw[] >>
    PROVE_TAC[] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    disj2_tac >>
    pop_assum mp_tac >>
    qmatch_abbrev_tac`a ==> b` >>
    qsuff_tac`a = b` >- rw[] >>
    unabbrev_all_tac >>
    rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
    simp[FUN_EQ_THM,inv_DEF] >>
    PROVE_TAC[]) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    disj2_tac >>
    pop_assum mp_tac >>
    qmatch_abbrev_tac`a ==> b` >>
    qsuff_tac`a = b` >- rw[] >>
    unabbrev_all_tac >> fs[] >>
    rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
    simp[FUN_EQ_THM,inv_DEF] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    ntac 2 (pop_assum mp_tac) >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    pop_assum mp_tac >> fs[MEM_ZIP] >>
    PROVE_TAC[]) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once syneq_cases] >>
    simp[inv_DEF] ) >>
  rw[] >>
  rw[Once syneq_cases] >>
  disj2_tac >> rw[] >>
  rfs[] >>
  res_tac >>
  map_every qexists_tac[`az`,`exp2`,`j2`,`r2`,`exp1`,`j1`,`r1`] >>
  simp[] >>
  rator_assum`syneq_exp`mp_tac >>
  qmatch_abbrev_tac`a ==> b` >>
  qsuff_tac`a = b` >- rw[] >>
  unabbrev_all_tac >> fs[] >>
  rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
  simp[FUN_EQ_THM,inv_DEF] >>
  PROVE_TAC[])

val syneq_mono_V = store_thm("syneq_mono_V",
  ``(∀c1 c2 x y. syneq c1 c2 x y ⇒ T) ∧
    (∀c1 c2 ez1 ez2 V exp1 exp2. syneq_exp c1 c2 ez1 ez2 V exp1 exp2 ⇒ ∀V'. (∀x y. V x y ∧ x < ez1 ∧ y < ez2 ⇒ V' x y) ⇒ syneq_exp c1 c2 ez1 ez2 V' exp1 exp2) ∧
    (∀c1 c2 ez1 ez2 V defs1 defs2. syneq_cb c1 c2 ez1 ez2 V defs1 defs2 ⇒
     ∀V'. (∀x y. V x y ∧ x < ez1 ∧ y < ez2 ⇒ V' x y) ⇒ syneq_cb c1 c2 ez1 ez2 V' defs1 defs2)``,
  ho_match_mp_tac syneq_ind >>
  rw[] >> simp[Once syneq_cases] >> rfs[] >>
  TRY ( disj2_tac >>
        first_x_assum (match_mp_tac o MP_CANON) >>
        simp[] >>
        srw_tac[ARITH_ss][] >>
        fsrw_tac[ARITH_ss][] >>
        PROVE_TAC[] ) >>
  TRY (
    disj2_tac >>
    rator_assum`EVERY2`mp_tac >>
    match_mp_tac EVERY2_mono >>
    simp[] ) >>
  disj2_tac >>
  rw[] >>
  res_tac >>
  rpt (qpat_assum`A = B`(mp_tac o SYM)) >>
  rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[] >>
  srw_tac[ARITH_ss][] >>
  fsrw_tac[ARITH_ss][] >>
  first_x_assum match_mp_tac >>
  Cases_on`EL n defs1`>>
  TRY (qmatch_assum_rename_tac`EL n defs1 = INL p`[] >> PairCases_on`p`) >>
  fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
  Cases_on`EL n defs2`>>
  TRY (qmatch_assum_rename_tac`EL n defs2 = INL p`[] >> PairCases_on`p`) >>
  fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
  rw[] >> rpt (qpat_assum `X = CCEnv Y` mp_tac) >> srw_tac[ARITH_ss][] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
  first_x_assum match_mp_tac >> simp[])

val syneq_trans = store_thm("syneq_trans",
  ``(∀c1 c2 x y. syneq c1 c2 x y ⇒ ∀c3 z. syneq c2 c3 y z ⇒ syneq c1 c3 x z) ∧
    (∀c1 c2 ez1 ez2 V e1 e2. syneq_exp c1 c2 ez1 ez2 V e1 e2 ⇒
      ∀c3 ez3 V' e3. syneq_exp c2 c3 ez2 ez3 V' e2 e3 ⇒ syneq_exp c1 c3 ez1 ez3 (V' O V) e1 e3) ∧
    (∀c1 c2 ez1 ez2 V d1 d2. syneq_cb c1 c2 ez1 ez2 V d1 d2 ⇒
      ∀c3 ez3 V' d3. syneq_cb c2 c3 ez2 ez3 V' d2 d3 ⇒ syneq_cb c1 c3 ez1 ez3 (V' O V) d1 d3)``,
  ho_match_mp_tac syneq_ind >>
  strip_tac >- rw[] >>
  strip_tac >- ( ntac 2 (rw[Once syneq_cases] ) ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[syneq_refl] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >> rw[] >>
    disj2_tac >- (
      qexists_tac`V` >>
      simp[] >>
      conj_tac >- PROVE_TAC[syneq_refl] >>
      first_x_assum(qspecl_then[`c2`,`LENGTH env2`,`$=`,`d2`]mp_tac) >>
      simp[Id_O] >> disch_then match_mp_tac >>
      simp[Once syneq_cases] ) >>
    qexists_tac`V' O V` >>
    simp[O_DEF] >>
    PROVE_TAC[]) >>
  strip_tac >- ( ntac 2 (rw[Once syneq_cases] ) ) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 (CONJUNCT2 syneq_mono_V))) >>
    qexists_tac`V'` >>
    simp[O_DEF] >> PROVE_TAC[] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD,O_DEF] >>
    PROVE_TAC[] ) >>
  strip_tac >- ( ntac 2 (rw[Once syneq_cases] ) ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >- (
      simp[O_DEF] >>
      disj2_tac >>
      conj_tac >- PROVE_TAC[syneq_rules] >>
      first_x_assum(qspecl_then[`c2`,`ez2+1`,`$=`,`e2'`]mp_tac) >>
      simp[Id_O,syneq_rules] >> strip_tac >>
      match_mp_tac (MP_CANON(CONJUNCT1(CONJUNCT2 syneq_mono_V))) >>
      HINT_EXISTS_TAC >>
      simp[O_DEF] >>
      srw_tac[DNF_ss,ARITH_ss][] >>
      HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][]) >>
    disj2_tac >>
    res_tac >>
    match_mp_tac (MP_CANON(CONJUNCT1(CONJUNCT2 syneq_mono_V))) >>
    HINT_EXISTS_TAC >>
    simp[O_DEF] >>
    srw_tac[DNF_ss,ARITH_ss][] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases,O_DEF] >> PROVE_TAC[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[syneq_rules] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    PROVE_TAC[syneq_rules]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    PROVE_TAC[syneq_rules]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >- (
      simp[O_DEF] >>
      disj2_tac >>
      conj_tac >- PROVE_TAC[syneq_rules] >>
      first_x_assum(qspecl_then[`c2`,`ez2+1`,`$=`,`e2'`]mp_tac) >>
      simp[Id_O,syneq_rules] >> strip_tac >>
      match_mp_tac (MP_CANON(CONJUNCT1(CONJUNCT2 syneq_mono_V))) >>
      HINT_EXISTS_TAC >>
      simp[O_DEF] >>
      srw_tac[DNF_ss,ARITH_ss][] >>
      HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][]) >>
    disj2_tac >>
    res_tac >>
    match_mp_tac (MP_CANON(CONJUNCT1(CONJUNCT2 syneq_mono_V))) >>
    HINT_EXISTS_TAC >>
    simp[O_DEF] >>
    srw_tac[DNF_ss,ARITH_ss][] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    rfs[] >> fs[] >> disj2_tac >- (
      conj_tac >- metis_tac[syneq_cb_refl] >>
      first_x_assum(qspecl_then[`c2`,`ez2 + LENGTH d1`,`$=`,`e2`]mp_tac) >>
      simp[syneq_exp_refl,O_DEF] >>
      strip_tac >>
      match_mp_tac (MP_CANON(CONJUNCT1(CONJUNCT2 syneq_mono_V))) >>
      HINT_EXISTS_TAC >>
      srw_tac[DNF_ss,ARITH_ss][] >>
      HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][]) >>
    res_tac >>
    match_mp_tac (MP_CANON(CONJUNCT1(CONJUNCT2 syneq_mono_V))) >>
    HINT_EXISTS_TAC >>
    simp[O_DEF] >>
    srw_tac[DNF_ss,ARITH_ss][] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    metis_tac[syneq_cb_refl]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >> rw[] >>
    rpt (qpat_assum` LENGTH X = LENGTH Y` mp_tac) >>
    rpt strip_tac >>
    fs[MEM_ZIP,FORALL_PROD] >>
    PROVE_TAC[syneq_exp_refl] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >> strip_tac >>
    simp[Once syneq_cases] >>
    metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac (MP_CANON(CONJUNCT2 (CONJUNCT2 syneq_mono_V))) >>
    simp[O_DEF] >> metis_tac[]) >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_cases] >> strip_tac >>
  simp[Once syneq_cases] >> disj2_tac >>
  fs[] >> rfs[] >> rw[] >> res_tac >>
  rpt (qpat_assum`A = B`(mp_tac o SYM)) >>
  rw[] >> fs[AC ADD_ASSOC ADD_SYM] >>
  match_mp_tac (MP_CANON(CONJUNCT1(CONJUNCT2 syneq_mono_V))) >- (
    first_x_assum(qspecl_then[`c2`,`az + j2`,`$=`,`e2`]mp_tac) >>
    simp[syneq_exp_refl] >> strip_tac >>
    HINT_EXISTS_TAC >>
    simp[O_DEF] >>
    srw_tac[DNF_ss,ARITH_ss][] >>
    qmatch_assum_rename_tac`V a b`[] >>
    qexists_tac`b` >>
    fsrw_tac[ARITH_ss][] >>
    first_x_assum match_mp_tac >>
    Cases_on`EL n d2`>>TRY(qmatch_assum_rename_tac`EL n d2 = INL p`[]>>Cases_on`p`)>>
    fsrw_tac[DNF_ss][syneq_cb_aux_def,LET_THM,UNCURRY] >> rw[] >> fs[] >>
    qpat_assum`X = CCEnv b`mp_tac >>
    srw_tac[ARITH_ss][] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    first_x_assum match_mp_tac >>
    srw_tac[ARITH_ss][]) >>
  rator_assum`syneq_exp`mp_tac >>
  qho_match_abbrev_tac`syneq_exp c2 c3 a1 a2 VV e1 e3 ⇒ Z` >>
  strip_tac >>
  first_x_assum(qspecl_then[`c3`,`a2`,`VV`,`e3`]mp_tac) >>
  simp[Abbr`Z`] >> strip_tac >>
  HINT_EXISTS_TAC >>
  simp[O_DEF] >>
  pop_assum kall_tac >>
  srw_tac[DNF_ss,ARITH_ss][Abbr`VV`] >> fs[]
  >- ( spose_not_then strip_assume_tac >> fs[] )
  >- ( spose_not_then strip_assume_tac >> fs[] ) >>
  metis_tac[])

val result_rel_syneq_refl = save_thm(
"result_rel_syneq_refl",
result_rel_refl
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [syneq_refl])
val _ = export_rewrites["result_rel_syneq_refl"]

val result_rel_syneq_trans = save_thm(
"result_rel_syneq_trans",
result_rel_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val result_rel_syneq_sym = save_thm(
"result_rel_syneq_sym",
result_rel_sym
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss[syneq_sym])

(* TODO: move *)
val EVERY2_trans = store_thm("EVERY2_trans",
  ``(!x y z. R x y /\ R y z ==> R x z) ==>
    !x y z. EVERY2 R x y /\ EVERY2 R y z ==> EVERY2 R x z``,
  SRW_TAC[][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] THEN
  REPEAT (Q.PAT_ASSUM`LENGTH X = Y`MP_TAC) THEN
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP] THEN
  METIS_TAC[])

val LIST_REL_EVERY2 = store_thm("LIST_REL_EVERY2",
  ``LIST_REL = EVERY2``,
  SRW_TAC[][FUN_EQ_THM] THEN
  METIS_TAC[EVERY2_EVERY,LIST_REL_EVERY_ZIP])

val EVERY2_LUPDATE_same = store_thm("EVERY2_LUPDATE_same",
  ``!P l1 l2 v1 v2 n. P v1 v2 /\ EVERY2 P l1 l2 ==>
    EVERY2 P (LUPDATE v1 n l1) (LUPDATE v2 n l2)``,
  GEN_TAC THEN Induct THEN
  SRW_TAC[][LUPDATE_def] THEN
  Cases_on`n`THEN SRW_TAC[][LUPDATE_def])

val EVERY2_refl = store_thm("EVERY2_refl",
  ``(!x. MEM x ls ==> R x x) ==> (EVERY2 R ls ls)``,
  Induct_on`ls` >>rw[])

val EVERY2_syneq_refl = save_thm("EVERY2_syneq_refl",
EVERY2_refl
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [syneq_refl])
val _ = export_rewrites["EVERY2_syneq_refl"]

val EVERY2_syneq_exp_refl = store_thm("EVERY2_syneq_exp_refl",
  ``(!x. x < z ⇒ V x x) ⇒ EVERY2 (syneq_exp c c z z V) ls ls``,
  strip_tac >>
  match_mp_tac EVERY2_refl >>
  rpt strip_tac >>
  match_mp_tac syneq_exp_refl >>
  first_assum ACCEPT_TAC)

val EVERY2_syneq_trans = save_thm(
"EVERY2_syneq_trans",
EVERY2_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val fmap_rel_syneq_trans = save_thm(
"fmap_rel_syneq_trans",
fmap_rel_trans
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
|> UNDISCH
|> (fn th => PROVE_HYP (PROVE[syneq_trans](hd(hyp th))) th)
|> SIMP_RULE std_ss [AND_IMP_INTRO])

val fmap_rel_syneq_sym = save_thm(
"fmap_rel_syneq_sym",
fmap_rel_sym
|> Q.GEN`R`
|> Q.ISPEC`syneq c c`
|> SIMP_RULE std_ss[syneq_sym])

val syneq_ov = store_thm("syneq_ov",
  ``(∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒ ∀m s. Cv_to_ov m s v1 = Cv_to_ov m s v2) ∧
    (∀vs1 vs2 c1 c2. EVERY2 (syneq c1 c2) vs1 vs2 ⇒ ∀m s. EVERY2 (λv1 v2. Cv_to_ov m s v1 = Cv_to_ov m s v2) vs1 vs2)``,
  ho_match_mp_tac(TypeBase.induction_of``:Cv``) >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_cases] >>
  rw[] >> rw[] >>
  rw[MAP_EQ_EVERY2] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rw[] >> TRY (
    first_x_assum (match_mp_tac o MP_CANON) >>
    metis_tac[] ) >>
  metis_tac[])

val syneq_lit_loc = store_thm("syneq_lit_loc",
  ``(syneq c1 c2 (CLitv l1) v2 = (v2 = CLitv l1)) ∧
    (syneq c1 c2 v1 (CLitv l2) = (v1 = CLitv l2)) ∧
    (syneq c1 c2 (CLoc n1) v2 = (v2 = CLoc n1)) ∧
    (syneq c1 c2 v1 (CLoc n2) = (v1 = CLoc n2))``,
  rw[] >> fs[Once syneq_cases] >> rw[EQ_IMP_THM])
val _ = export_rewrites["syneq_lit_loc"]

(* Misc. int lang lemmas *)

val good_cmap_def = Define`
  good_cmap cenv m =
    ∀c1 n1 c2 n2 s.
      MEM (c1,(n1,s)) cenv ∧
      MEM (c2,(n2,s)) cenv ∧
      (FAPPLY m c1 = FAPPLY m c2) ⇒ (c1 = c2)`

val Cevaluate_list_LENGTH = store_thm("Cevaluate_list_LENGTH",
  ``∀exps c s env s' vs. Cevaluate_list c s env exps (s', Rval vs) ⇒ (LENGTH vs = LENGTH exps)``,
  Induct >> rw[LENGTH_NIL] >> pop_assum mp_tac >>
  rw[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][] >>
  first_x_assum match_mp_tac >>
  srw_tac[SATISFY_ss][])

val FINITE_free_vars = store_thm(
"FINITE_free_vars",
``(∀t. FINITE (free_vars t)) ∧ (∀b. FINITE (cbod_fvs b))``,
ho_match_mp_tac free_vars_ind >>
rw[free_vars_def] >>
rw[FOLDL_UNION_BIGUNION] >>
TRY (match_mp_tac IMAGE_FINITE >> match_mp_tac FINITE_DIFF) >>
metis_tac[])
val _ = export_rewrites["FINITE_free_vars"]

val Cevaluate_store_SUBSET = store_thm("Cevaluate_store_SUBSET",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒ LENGTH s ≤ LENGTH (FST res)) ∧
    (∀c s env exps res. Cevaluate_list c s env exps res ⇒ LENGTH s ≤ LENGTH (FST res))``,
  ho_match_mp_tac Cevaluate_ind >> rw[] >>
  TRY (PROVE_TAC [LESS_EQ_TRANS]) >- (
    Cases_on`uop`>>rw[]>>srw_tac[ARITH_ss][] >>
    Cases_on`v`>>rw[] ) >>
  Cases_on`v1`>>rw[])

val all_Clocs_def = tDefine "all_Clocs"`
  (all_Clocs (CLitv _) = {}) ∧
  (all_Clocs (CConv _ vs) = BIGUNION (IMAGE all_Clocs (set vs))) ∧
  (all_Clocs (CRecClos env _ _) = BIGUNION (IMAGE all_Clocs (set env))) ∧
  (all_Clocs (CLoc n) = {n})`
  (WF_REL_TAC`measure Cv_size` >>
   srw_tac[ARITH_ss][Cv1_size_thm] >>
   Q.ISPEC_THEN`Cv_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val _ = export_rewrites["all_Clocs_def"]

val CevalPrim2_Clocs = store_thm("CevaluatePrim2_Clocs",
  ``∀p2 v1 v2 v. (CevalPrim2 p2 v1 v2 = Rval v) ⇒ (all_Clocs v = {})``,
  Cases >> fs[] >> Cases >> fs[] >>
  TRY (Cases_on`l` >> fs[] >> Cases >> fs[] >> Cases_on `l` >> fs[] >> rw[] >> rw[]) >>
  Cases >> fs[] >> rw[] >> rw[])

val Cevaluate_Clocs = store_thm("Cevaluate_Clocs",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s)
     ⇒
     BIGUNION (IMAGE all_Clocs (set (FST res))) ⊆ count (LENGTH (FST res)) ∧
     ∀v. (SND res = Rval v) ⇒ all_Clocs v ⊆ count (LENGTH (FST res))) ∧
    (∀c s env exps res. Cevaluate_list c s env exps res ⇒
     BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
     BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s)
     ⇒
     BIGUNION (IMAGE all_Clocs (set (FST res))) ⊆ count (LENGTH (FST res)) ∧
     ∀vs. (SND res = Rval vs) ⇒ BIGUNION (IMAGE all_Clocs (set vs)) ⊆ count (LENGTH (FST res)))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,FST,LESS_LESS_EQ_TRANS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- srw_tac[ETA_ss][] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    srw_tac[ETA_ss][] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
    PROVE_TAC[] ) >>
  strip_tac >- srw_tac[ETA_ss][] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases_on`cb`>>fs[LET_THM] >- (
      PairCases_on`x`>>fs[]>>
      fsrw_tac[DNF_ss][MEM_GENLIST]>>
      imp_res_tac Cevaluate_store_SUBSET >>
      fs[] >> metis_tac[LESS_LESS_EQ_TRANS] ) >>
    fsrw_tac[DNF_ss][MEM_MAP,IN_FRANGE,UNCURRY] >>
    rfs[] >>
    imp_res_tac Cevaluate_store_SUBSET >>
    fsrw_tac[ARITH_ss][] >>
    reverse conj_tac >- metis_tac[LESS_LESS_EQ_TRANS] >>
    conj_tac >- metis_tac[LESS_LESS_EQ_TRANS] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
    metis_tac[LESS_LESS_EQ_TRANS]) >>
  strip_tac >- (
    rw[] >> fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    Cases_on`uop`>>fs[LET_THM] >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      rw[] >> res_tac >>
      fsrw_tac[ARITH_ss][]) >>
    Cases_on`v`>>fs[] >>
    rw[el_check_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> imp_res_tac CevalPrim2_Clocs >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 6 gen_tac >>
    Cases >> fs[] >>
    gen_tac >> ntac 2 strip_tac >>
    fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    rw[] >> imp_res_tac MEM_LUPDATE >>
    fsrw_tac[DNF_ss][] >> res_tac) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST]) >>
  strip_tac >- rw[] >>
  rw[] >> fs[] >> rfs[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  metis_tac[Cevaluate_store_SUBSET,LESS_LESS_EQ_TRANS,FST])

(* simple cases of syneq preservation *)

val Cv_ind = store_thm("Cv_ind",
  ``∀P. (∀l. P (CLitv l)) ∧ (∀n vs. EVERY P vs ⇒ P (CConv n vs)) ∧
        (∀env defs n. EVERY P env ⇒ P (CRecClos env defs n)) ∧
        (∀n. P (CLoc n)) ⇒
        ∀v. P v``,
  rw[] >>
  qsuff_tac `(∀v. P v) ∧ (∀vs. EVERY P vs)` >- rw[] >>
  ho_match_mp_tac(TypeBase.induction_of``:Cv``) >>
  simp[])

val syneq_no_closures = store_thm("syneq_no_closures",
``∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒ (no_closures v2 = no_closures v1)``,
  ho_match_mp_tac Cv_ind >>
  rw[] >> pop_assum mp_tac >>
  simp[Once syneq_cases] >>
  rw[] >> rw[] >>
  srw_tac[ETA_ss][] >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  pop_assum mp_tac >>
  fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL] >>
  metis_tac[])

val no_closures_syneq_equal = store_thm("no_closures_syneq_equal",
``∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒ no_closures v1 ⇒ (v1 = v2)``,
  ho_match_mp_tac Cv_ind >>
  rw[] >>
  pop_assum mp_tac >> simp[Once syneq_cases] >>
  pop_assum mp_tac >> simp[Once syneq_cases] >>
  rw[] >> fsrw_tac[ETA_ss,DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  ntac 2 (pop_assum mp_tac) >>
  fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL,LIST_EQ_REWRITE] >>
  metis_tac[])

val CevalPrim2_syneq_equal = store_thm(
"CevalPrim2_syneq_equal",
``∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒
    ∀p v. (CevalPrim2 p v v1 = CevalPrim2 p v v2) ∧
          (CevalPrim2 p v1 v = CevalPrim2 p v2 v)``,
ho_match_mp_tac Cv_ind >>
strip_tac >- ( rw[Once syneq_cases] ) >>
strip_tac >- (
  gen_tac >> qx_gen_tac`vs1` >>
  strip_tac >>
  simp[Once syneq_cases] >>
  rpt gen_tac >> strip_tac >- metis_tac[] >>
  `no_closures (CConv cn vs1) = no_closures (CConv cn vs2)` by (
    match_mp_tac syneq_no_closures >>
    simp[Once syneq_cases] >>
    fsrw_tac[][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    qpat_assum`LENGTH vs1 = x`assume_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP] >>
    PROVE_TAC[syneq_sym]) >>
  `no_closures (CConv cn vs2) ⇒ (vs1 = vs2)` by (
    strip_tac >>
    qsuff_tac `CConv cn vs1 = CConv cn vs2` >- rw[] >>
    match_mp_tac (MP_CANON no_closures_syneq_equal) >>
    rw[Once syneq_cases] >> PROVE_TAC[] ) >>
  fs[] >>
  Cases >> Cases >> TRY (Cases_on `l`) >> rw[] ) >>
strip_tac >- (
  rpt gen_tac >> strip_tac >>
  simp[Once syneq_cases] >>
  rpt gen_tac >> strip_tac >>
  Cases >> Cases >> TRY (Cases_on `l`) >> rw[] ) >>
simp[Once syneq_cases])

val doPrim2_syneq = store_thm(
"doPrim2_syneq",
``∀v1 v2 c1 c2. syneq c1 c2 v1 v2 ⇒
    ∀b ty op v. (doPrim2 b ty op v v1 = doPrim2 b ty op v v2) ∧
                (doPrim2 b ty op v1 v = doPrim2 b ty op v2 v)``,
ho_match_mp_tac Cv_ind >>
rw[] >> pop_assum mp_tac >>
simp[Once syneq_cases] >> rw[] >>
Cases_on `v` >> rw[])

(* TODO: move *)
val EVERY2_RC_same = store_thm("EVERY2_RC_same",
  ``EVERY2 (RC R) l l``,
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF])
val _ = export_rewrites["EVERY2_RC_same"]
val syneq_strongind = CompileTheory.syneq_strongind

val CevalPrim2_syneq = store_thm("CevalPrim2_syneq",
  ``∀c1 c2 p2 v11 v21 v12 v22.
    syneq c1 c2 v11 v12 ∧ syneq c1 c2 v21 v22 ⇒
    result_rel (syneq c1 c2) (CevalPrim2 p2 v11 v21) (CevalPrim2 p2 v12 v22)``,
  ntac 2 gen_tac >>
  Cases >> simp[] >>
  Cases >> Cases >>
  simp[] >>
  TRY ( simp[Once syneq_cases] >> fsrw_tac[DNF_ss][] >> NO_TAC) >>
  TRY ( simp[Once (CONJUNCT1 syneq_cases)] >> simp[Once (CONJUNCT1 syneq_cases),SimpR``$/\``] >> fsrw_tac[DNF_ss][] >> NO_TAC) >>
  TRY (Cases_on`l` >> Cases_on`l'` >> simp[] >> fsrw_tac[DNF_ss][i0_def] >> rw[] >> NO_TAC) >>
  TRY ( rw[] >> NO_TAC ) >>
  TRY (
    rw[] >>
    spose_not_then strip_assume_tac >>
    imp_res_tac syneq_no_closures >>
    fs[Once syneq_cases] >> rw[] >>
    metis_tac[NOT_EVERY] ) >>
  simp[Once syneq_cases] >>
  simp[Once syneq_cases] >>
  rpt strip_tac >>
  srw_tac[ETA_ss][] >>
  fsrw_tac[DNF_ss][EVERY_MEM,EVERY2_EVERY,FORALL_PROD,EXISTS_MEM] >>
  rfs[MEM_ZIP] >>
  fsrw_tac[DNF_ss][MEM_EL] >>
  metis_tac[no_closures_syneq_equal,syneq_no_closures,LIST_EQ_REWRITE])

val CevalPrim1_syneq = store_thm("CevalPrim1_syneq",
  ``∀c1 c2 uop s1 s2 v1 v2. EVERY2 (syneq c1 c2) s1 s2 ∧ syneq c1 c2 v1 v2 ⇒
    EVERY2 (syneq c1 c2) (FST (CevalPrim1 uop s1 v1)) (FST (CevalPrim1 uop s2 v2)) ∧
    result_rel (syneq c1 c2) (SND (CevalPrim1 uop s1 v1)) (SND (CevalPrim1 uop s2 v2))``,
  ntac 2 gen_tac >>
  Cases >- (
    simp[] >> rw[] >> fs[EVERY2_EVERY] >> lrw[GSYM ZIP_APPEND] ) >>
  ntac 2 gen_tac >>
  Cases >> simp[Once syneq_cases] >>
  fsrw_tac[DNF_ss][] >>
  rw[el_check_def,EVERY2_EVERY] >>
  rfs[EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
  fsrw_tac[DNF_ss][])

val CevalUpd_syneq = store_thm(
"CevalUpd_syneq",
``∀c1 c2 s1 v1 v2 s2 w1 w2.
  syneq c1 c2 v1 w1 ∧ syneq c1 c2 v2 w2 ∧ EVERY2 (syneq c1 c2) s1 s2 ⇒
  EVERY2 (syneq c1 c2) (FST (CevalUpd s1 v1 v2)) (FST (CevalUpd s2 w1 w2)) ∧
  result_rel (syneq c1 c2) (SND (CevalUpd s1 v1 v2)) (SND (CevalUpd s2 w1 w2))``,
  ntac 3 gen_tac >>
  Cases >> simp[] >>
  ntac 2 gen_tac >>
  Cases >> simp[] >>
  rw[] >> TRY (
    match_mp_tac EVERY2_LUPDATE_same >>
    rw[] ) >>
  PROVE_TAC[EVERY2_EVERY])

val Cevaluate_syneq = store_thm("Cevaluate_syneq",
  ``(∀c1 s1 env1 exp1 res1. Cevaluate c1 s1 env1 exp1 res1 ⇒
      ∀c2 ez1 ez2 V s2 env2 exp2 res2.
        syneq_exp c1 c2 (LENGTH env1) (LENGTH env2) V exp1 exp2
      ∧ (∀v1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ⇒ syneq c1 c2 (EL v1 env1) (EL v2 env2))
      ∧ EVERY2 (syneq c1 c2) s1 s2
      ⇒ ∃res2.
        Cevaluate c2 s2 env2 exp2 res2 ∧
        EVERY2 (syneq c1 c2) (FST res1) (FST res2) ∧
        result_rel (syneq c1 c2) (SND res1) (SND res2)) ∧
    (∀c1 s1 env1 es1 res1. Cevaluate_list c1 s1 env1 es1 res1 ⇒
      ∀c2 ez1 ez2 V s2 env2 es2 res2.
        EVERY2 (syneq_exp c1 c2 (LENGTH env1) (LENGTH env2) V) es1 es2
      ∧ (∀v1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ⇒ syneq c1 c2 (EL v1 env1) (EL v2 env2))
      ∧ EVERY2 (syneq c1 c2) s1 s2
      ⇒ ∃res2.
        Cevaluate_list c2 s2 env2 es2 res2 ∧
        EVERY2 (syneq c1 c2) (FST res1) (FST res2) ∧
        result_rel (EVERY2 (syneq c1 c2)) (SND res1) (SND res2))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- ( simp[Once syneq_cases] >> rw[] >> rw[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj1_tac >>
      first_x_assum match_mp_tac >>
      qexists_tac`$=` >>
      simp[syneq_exp_refl] ) >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2'`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >> disj1_tac >>
      last_x_assum(qspecl_then[`c1`,`$=`,`s2`,`env2`,`exp1`]mp_tac) >>
      simp[syneq_exp_refl] >>
      disch_then(Q.X_CHOOSE_THEN`s2'`strip_assume_tac) >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`n`,`s2'`] >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      simp[] >>
      first_x_assum match_mp_tac >>
      qexists_tac`$=` >>
      simp[syneq_exp_refl,ADD1] >>
      Cases >> simp[ADD1]) >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> fsrw_tac[DNF_ss][] >>
    qx_gen_tac`s3` >> strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp c1 c2 (k1+1) (k2+1) V' e' b` >>
    first_x_assum(qspecl_then[`c2`,`V'`,`s3`,`CLitv (IntLit n)::env2`,`b`]mp_tac) >>
    simp[Abbr`V'`,ADD1] >>
    fsrw_tac[DNF_ss,ARITH_ss][] >>
    qmatch_abbrev_tac`(p ⇒ q) ⇒ r` >>
    `p` by (
      map_every qunabbrev_tac[`p`,`q`,`r`] >>
      rpt conj_tac >> Cases >> simp[] >>
      Cases >> simp[ADD1] >> PROVE_TAC[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`p`,`q`,`r`] >>
    simp[EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj2_tac >>
      first_x_assum match_mp_tac >>
      qexists_tac`$=` >>
      simp[syneq_exp_refl] ) >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2'`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    rw[] >> simp[] >> metis_tac[syneq_exp_refl]) >>
  strip_tac >- (
    simp[Once syneq_cases] >>
    rw[] >> rw[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      simp[Once syneq_cases] >>
      fsrw_tac[DNF_ss][] >>
      disj2_tac >>
      first_x_assum match_mp_tac >>
      qexists_tac`$=` >>
      rw[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
      rw[syneq_exp_refl]) >>
    qx_gen_tac`es2` >>
    strip_tac >>
    simp[Once syneq_cases] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj2_tac >>
    first_x_assum match_mp_tac >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum match_mp_tac >>
    TRY (metis_tac[]) >>
    qexists_tac`$=` >> simp[] >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
    rw[] >> rw[syneq_exp_refl] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      first_x_assum(qspecl_then[`c1`,`V`,`s2`,`env2`,`exp1`]mp_tac) >>
      simp[syneq_exp_refl] >>
      simp[Once syneq_cases] >>
      fsrw_tac[DNF_ss][] >> strip_tac >>
      rpt strip_tac >>
      PROVE_TAC[] ) >>
    qx_gen_tac`e2` >> rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[Once(CONJUNCT1 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    rw[] >- (
      first_x_assum match_mp_tac >>
      metis_tac[syneq_exp_refl] ) >>
    simp[Once Cevaluate_cases] >>
    first_x_assum match_mp_tac >>
    metis_tac[syneq_exp_refl] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    conj_tac >- (
      rw[] >>
      first_x_assum(qspecl_then[`c1`,`V`,`s2`,`env2`,`exp1`]mp_tac) >>
      fsrw_tac[DNF_ss][syneq_exp_refl] >>
      simp[Once syneq_cases] >>
      fsrw_tac[DNF_ss][] >>
      rw[] >>
      fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >- (
        qmatch_assum_rename_tac`LENGTH s' = LENGTH z`[] >>
        map_every qexists_tac[`z`,`m`,`vs`] >>
        simp[] ) >>
      simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      metis_tac[syneq_refl,MEM_ZIP] ) >>
    qx_gen_tac`e2` >> rw[] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[Once (CONJUNCT1 syneq_cases)] >>
    rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    metis_tac[syneq_refl,MEM_ZIP]) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[syneq_exp_refl] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- (
      rw[Once Cevaluate_cases] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      disj1_tac >>
      last_x_assum(qspecl_then[`c1`,`$=`,`s2`,`env2`,`exp1`]mp_tac) >>
      simp[syneq_exp_refl] >>
      disch_then(Q.X_CHOOSE_THEN`s2'`strip_assume_tac) >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`v'`,`s2'`] >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      simp[] >>
      first_x_assum match_mp_tac >>
      qexists_tac`$=` >>
      simp[syneq_exp_refl,ADD1] >>
      Cases >> simp[ADD1]) >>
    map_every qx_gen_tac[`e`,`b`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e`]mp_tac) >>
    simp[EXISTS_PROD] >> fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`s3`,`v3`] >> strip_tac >>
    qmatch_assum_abbrev_tac`syneq_exp c1 c2 (k1+1) (k2+1) V' e' b` >>
    first_x_assum(qspecl_then[`c2`,`V'`,`s3`,`v3::env2`,`b`]mp_tac) >>
    simp[Abbr`V'`,ADD1] >>
    fsrw_tac[DNF_ss,ARITH_ss][] >>
    qmatch_abbrev_tac`(p ⇒ q) ⇒ r` >>
    `p` by (
      map_every qunabbrev_tac[`p`,`q`,`r`] >>
      rpt conj_tac >> Cases >> simp[] >>
      Cases >> simp[ADD1] >> PROVE_TAC[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`p`,`q`,`r`] >>
    simp[EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >- (
      rw[] >> disj2_tac >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      metis_tac[syneq_exp_refl] ) >>
    map_every qx_gen_tac[`e2`,`b2`] >>
    rw[] >> fsrw_tac[DNF_ss][] >>
    disj2_tac >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_tac >- (
      rw[] >>
      simp[Once Cevaluate_cases] >>
      simp[GSYM CONJ_ASSOC] >>
      simp[RIGHT_EXISTS_AND_THM] >>
      conj_tac >- (
        simp[EVERY_MEM,MEM_EL] >>
        rfs[] >> simp_tac(std_ss++QUANT_INST_ss[std_qp])[GSYM LEFT_FORALL_IMP_THM] >>
        qx_gen_tac`d` >> strip_tac >>
        gen_tac >> strip_tac >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
        metis_tac[] ) >>
      first_x_assum match_mp_tac >>
      qexists_tac`$=` >>
      simp[syneq_exp_refl] >>
      rw[] >>
      Cases_on`v2 < LENGTH defs` >>
      lrw[REVERSE_GENLIST,EL_GENLIST,EL_APPEND1,EL_APPEND2] >>
      simp[Once syneq_cases] >> disj2_tac >>
      qexists_tac`λv1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env1` >>
      simp[syneq_cb_refl] ) >>
    map_every qx_gen_tac[`defs2`,`b2`] >>
    strip_tac >>
    simp[Once Cevaluate_cases] >>
    simp[GSYM CONJ_ASSOC] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- (
      simp[EVERY_MEM,MEM_EL] >>
      rfs[] >> simp_tac(std_ss++QUANT_INST_ss[std_qp])[GSYM LEFT_FORALL_IMP_THM] >>
      qx_gen_tac`d` >> strip_tac >>
      gen_tac >> strip_tac >>
      rator_assum`syneq_cb`mp_tac >>
      simp[Once syneq_cases] >>
      strip_tac >- (
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] >>
        metis_tac[] ) >>
      pop_assum (qspec_then`d`mp_tac) >>
      simp[syneq_cb_aux_def] >>
      rw[UNCURRY] >> rw[] ) >>
    first_x_assum match_mp_tac >>
    simp[] >> rfs[] >>
    simp[ADD_SYM] >>
    HINT_EXISTS_TAC >>
    simp[] >>
    rw[] >>
    lrw[EL_APPEND1,EL_APPEND2,REVERSE_GENLIST,EL_GENLIST] >>
    simp[Once syneq_cases] >>
    disj2_tac >>
    qexists_tac`λv1 v2. V v1 v2 ∧ v1 < LENGTH env1 ∧ v2 < LENGTH env2` >> rw[] >>
    match_mp_tac (MP_CANON (CONJUNCT2 (CONJUNCT2 syneq_mono_V))) >>
    qexists_tac`V` >> simp[]) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    rw[] >> simp[] >>
    simp[Once syneq_cases] >- (
      disj2_tac >>
      qexists_tac`λv1 v2. v1 < LENGTH env1 ∧ v2 < LENGTH env2 ∧ (v1 = v2)` >>
      simp[syneq_refl,syneq_cb_refl] ) >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      rator_assum`syneq_cb`mp_tac >>
      simp[Once syneq_cases] >>
      simp[syneq_cb_aux_def] >>
      rw[UNCURRY] >> rw[] ) >>
    disj2_tac >>
    qexists_tac`λv1 v2. v1 < LENGTH env1 ∧ v2 < LENGTH env2 ∧ V v1 v2`>>rw[]>>
    match_mp_tac(MP_CANON(CONJUNCT2(CONJUNCT2(syneq_mono_V)))) >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    map_every qx_gen_tac[`e2`,`es2`] >>
    strip_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    simp[EXISTS_PROD] >>
    simp[Once syneq_cases] >>
    simp_tac(std_ss++DNF_ss)[] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      qmatch_assum_rename_tac`EVERY2 (syneq c1 c1) s1' s2'`[] >>
      qexists_tac`s2'` >> simp[] >>
      qexists_tac`λv1 v2. v1 < LENGTH cenv ∧ (v2 = v1)` >>
      map_every qexists_tac[`cenv`,`defs`] >>
      simp[] >>
      simp[syneq_cb_refl] ) >>
    map_every qx_gen_tac[`s2'`,`V'`,`cenv2`,`defs2`] >>
    strip_tac >>
    CONV_TAC(RESORT_EXISTS_CONV (fn ls => (List.drop(ls,2)@List.take(ls,2)))) >>
    map_every qexists_tac[`s2'`,`cenv2`,`defs2`,`n`] >>
    simp[] >>
    first_x_assum(qspecl_then[`c2`,`V`,`s2'`,`env2`,`es2`]mp_tac) >>
    simp[] >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    simp[EXISTS_PROD] >>
    simp_tac(std_ss++DNF_ss)[] >>
    map_every qx_gen_tac[`s2''`,`vs2`] >>
    strip_tac >>
    CONV_TAC(RESORT_EXISTS_CONV (fn ls => (List.drop(ls,2)@List.take(ls,2)))) >>
    map_every qexists_tac[`s2''`,`vs2`] >>
    rator_k_assum`syneq_cb`mp_tac >>
    simp_tac std_ss [Once syneq_cases] >>
    strip_tac >- (
      fsrw_tac[][LET_THM] >>
      Cases_on`EL n defs`>>TRY(qmatch_assum_rename_tac`EL n defs = INL z`[]>>Cases_on`z`)>>
      fs[syneq_cb_aux_def,LET_THM,UNCURRY] >- (
        rw[] >> fs[EVERY2_EVERY] >>
        fsrw_tac[DNF_ss][EXISTS_PROD] >>
        first_x_assum match_mp_tac >>
        simp[] >>
        qexists_tac`$=` >>
        simp[syneq_exp_refl] >>
        rfs[EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
        fsrw_tac[DNF_ss][] >>
        qx_gen_tac`v` >> strip_tac >>
        fs[]>>rfs[] >>
        Cases_on`v < LENGTH vs2`>>
        lrw[REVERSE_GENLIST,EL_APPEND1,EL_APPEND2,EL_REVERSE] >>
        Cases_on`v < LENGTH vs2 + LENGTH defs`>>
        lrw[EL_APPEND2,LENGTH_REVERSE,EL_APPEND1,LENGTH_GENLIST] >>
        simp[Once syneq_cases] >> disj2_tac >>
        qexists_tac`λv1 v2. v1 < LENGTH cenv ∧ v2 < LENGTH cenv ∧ V' v1 v2` >>
        simp[] >>
        match_mp_tac(MP_CANON(CONJUNCT2(CONJUNCT2 syneq_mono_V))) >>
        qexists_tac`V'` >>
        simp[] ) >>
      rw[] >> fs[EVERY2_EVERY] >>
      fsrw_tac[DNF_ss][EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      simp[] >>
      qexists_tac`$=` >>
      simp[syneq_exp_refl] >>
      rfs[EVERY_MEM,MEM_ZIP,FORALL_PROD] >>
      fsrw_tac[DNF_ss][] >>
      qx_gen_tac`v` >> strip_tac >>
      fs[]>>rfs[] >>
      Cases_on`v < LENGTH vs2`>>
      lrw[REVERSE_GENLIST,EL_APPEND1,EL_APPEND2,EL_REVERSE] >>
      Cases_on`v = LENGTH vs2`>>
      lrw[EL_APPEND2,LENGTH_REVERSE,EL_APPEND1,LENGTH_GENLIST] >- (
        simp[Once syneq_cases] >> disj2_tac >>
        qexists_tac`V'`>>simp[] >> metis_tac[] ) >>
      Cases_on`v < LENGTH vs2 + 1 + LENGTH (FST (c1 ' y).cd.ceenv)` >>
      lrw[EL_APPEND2,LENGTH_REVERSE,EL_APPEND1,LENGTH_GENLIST,EL_MAP] >- (
        simp[Once syneq_cases] >> disj2_tac >>
        qexists_tac`V'`>>simp[] >> metis_tac[] ) >>
      first_x_assum match_mp_tac >>
      first_x_assum match_mp_tac >>
      fsrw_tac[DNF_ss][MEM_EL] >>
      last_x_assum match_mp_tac >>
      simp[] ) >>
    pop_assum(qspec_then`n`mp_tac) >>
    simp[] >>
    Cases_on`EL n defs2` >- (
      Cases_on`x`>> simp[syneq_cb_aux_def] >>
      Cases_on`EL n defs` >- (
        Cases_on`x`>>fs[syneq_cb_aux_def] >>
        simp[] >> fs[] >> rw[] >>
        `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
        fs[EXISTS_PROD] >>
        first_x_assum match_mp_tac >>
        fs[AC ADD_ASSOC ADD_SYM] >>
        rator_assum`syneq_exp`mp_tac >>
        qho_match_abbrev_tac`syneq_exp c1 c2 ez1 ez2 V2 ee1 ee2 ⇒ P` >>
        strip_tac >> simp[Abbr`P`] >>
        qexists_tac`V2` >>
        simp[Abbr`ez1`,Abbr`ez2`] >> rfs[] >>
        rpt gen_tac >>
        pop_assum kall_tac >>
        fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
        fsrw_tac[DNF_ss][MEM_ZIP] >>
        simp[Abbr`V2`] >> rw[] >>
        TRY(`v1=v2` by (
          ntac 7 (pop_assum mp_tac) >>
          rpt (pop_assum kall_tac) >>
          ntac 4 strip_tac >>
          REWRITE_TAC[SUB_PLUS] >>
          simp[] >> NO_TAC ) >>
          qpat_assum`LENGTH defs2 - X = Y`kall_tac) >>
        lrw[EL_APPEND1,EL_APPEND2,EL_REVERSE,PRE_SUB1] >>
        TRY (first_x_assum match_mp_tac >> simp[] >> NO_TAC) >>
        simp[Once syneq_cases] >>
        disj2_tac >>
        qexists_tac`V'` >>
        fsrw_tac[DNF_ss][] >>
        metis_tac[] ) >>
      fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
      rw[] >>
      qpat_assum`LENGTH vs = X`(assume_tac o SYM) >>fs[] >>
      `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
      fs[EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      rator_assum`syneq_exp`mp_tac >>
      qho_match_abbrev_tac`syneq_exp c1 c2 ez1 ez2 V2 ee1 ee2 ⇒ P` >>
      strip_tac >> simp[Abbr`P`] >>
      qexists_tac`V2` >>
      simp[Abbr`ez1`,Abbr`ez2`] >> rfs[] >>
      fsrw_tac[ARITH_ss][] >>
      pop_assum kall_tac >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      fsrw_tac[DNF_ss][MEM_ZIP] >>
      simp[Abbr`V2`] >> rw[] >>
      lrw[EL_APPEND1,EL_APPEND2,EL_REVERSE,PRE_SUB1,EL_MAP] >>
      TRY (first_x_assum match_mp_tac >> simp[] >> NO_TAC) >- (
        `v1 = LENGTH vs` by fsrw_tac[ARITH_ss][] >> rw[] >>
        simp[Once syneq_cases] >>
        disj2_tac >>
        qexists_tac`V'` >>
        simp[] >> metis_tac[] ) >>
      simp[Once syneq_cases] >>
      disj2_tac >>
      qexists_tac`V'` >>
      simp[] >> metis_tac[] ) >>
    Cases_on`EL n defs` >- (
      Cases_on`x`>>fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
      rw[] >>
      qpat_assum`LENGTH vs = X`(assume_tac o SYM) >>fs[] >>
      `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
      fs[EXISTS_PROD] >>
      first_x_assum match_mp_tac >>
      rator_assum`syneq_exp`mp_tac >>
      qho_match_abbrev_tac`syneq_exp c1 c2 ez1 ez2 V2 ee1 ee2 ⇒ P` >>
      strip_tac >> simp[Abbr`P`] >>
      qexists_tac`V2` >>
      simp[Abbr`ez1`,Abbr`ez2`] >> rfs[] >>
      fsrw_tac[ARITH_ss][] >>
      pop_assum kall_tac >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      fsrw_tac[DNF_ss][MEM_ZIP] >>
      simp[Abbr`V2`] >> rw[] >>
      lrw[EL_APPEND1,EL_APPEND2,EL_REVERSE,PRE_SUB1,EL_MAP] >>
      TRY (first_x_assum match_mp_tac >> simp[] >> NO_TAC) >- (
        `v2 = LENGTH vs` by fsrw_tac[ARITH_ss][] >> rw[] >>
        simp[Once syneq_cases] >>
        disj2_tac >>
        qexists_tac`V'` >>
        simp[] >> metis_tac[] ) >>
      simp[Once syneq_cases] >>
      disj2_tac >>
      qexists_tac`V'` >>
      simp[] >> metis_tac[] ) >>
    fs[syneq_cb_aux_def,LET_THM,UNCURRY] >>
    rw[] >>
    qpat_assum`LENGTH vs = X`(assume_tac o SYM) >>fs[] >>
    `LENGTH vs2 = LENGTH vs` by fs[EVERY2_EVERY] >> fs[] >>
    fs[EXISTS_PROD] >>
    first_x_assum match_mp_tac >>
    rator_assum`syneq_exp`mp_tac >>
    qho_match_abbrev_tac`syneq_exp c1 c2 ez1 ez2 V2 ee1 ee2 ⇒ P` >>
    strip_tac >> simp[Abbr`P`] >>
    qexists_tac`V2` >>
    simp[Abbr`ez1`,Abbr`ez2`] >> rfs[] >>
    fsrw_tac[ARITH_ss][] >>
    pop_assum kall_tac >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    fsrw_tac[DNF_ss][MEM_ZIP] >>
    `LENGTH vs = LENGTH vs2` by rw[] >>
    qpat_assum`LENGTH vs = Y.az`kall_tac >>
    qpat_assum`LENGTH vs2 = Y.az`(assume_tac o SYM) >>
    simp[Abbr`V2`] >> rw[] >>
    lrw[EL_APPEND1,EL_APPEND2,EL_REVERSE,PRE_SUB1,EL_MAP] >>
    TRY (first_x_assum match_mp_tac >> simp[] >> NO_TAC) >- (
      `v1 = LENGTH vs2` by fsrw_tac[ARITH_ss][] >> rw[] >>
      `v2 = LENGTH vs2` by fsrw_tac[ARITH_ss][] >> rw[] >>
      simp[Once syneq_cases] >>
      disj2_tac >>
      qexists_tac`V'` >>
      simp[] >> metis_tac[] )
    >- (
      `v1 = LENGTH vs2` by fsrw_tac[ARITH_ss][] >> rw[] >>
      simp[Once syneq_cases] >>
      disj2_tac >>
      qexists_tac`V'` >>
      simp[] >> metis_tac[] )
    >- (
      `v2 = LENGTH vs2` by fsrw_tac[ARITH_ss][] >> rw[] >>
      simp[Once syneq_cases] >>
      disj2_tac >>
      qexists_tac`V'` >>
      simp[] >> metis_tac[] ) >>
    simp[Once syneq_cases] >>
    disj2_tac >>
    qexists_tac`V'` >>
    simp[] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    map_every qx_gen_tac[`e2`,`es2`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >>
    disch_then(mp_tac o UNDISCH_ALL) >>
    fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    map_every qx_gen_tac[`e2`,`es2`] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj2_tac >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[CevalPrim1_syneq] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj1_tac >>
    metis_tac[CevalPrim2_syneq] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[CevalUpd_syneq] ) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >> (
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e12`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    rw[] >>
    qmatch_assum_abbrev_tac`Cevaluate c2 s2 env2 e12 (s3,Rval (CLitv (Bool b)))` >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`b`,`s3`] >>
    simp[Abbr`b`] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    first_x_assum match_mp_tac >>
    metis_tac[] )) >>
  strip_tac >- (
    rw[] >>
    rator_assum`syneq_exp`mp_tac >>
    simp[Once (CONJUNCT2 syneq_cases)] >>
    fsrw_tac[DNF_ss][] >>
    conj_asm2_tac >- (
      rpt strip_tac >> fs[] >>
      first_x_assum match_mp_tac >>
      simp[syneq_exp_refl,EVERY2_syneq_exp_refl] ) >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj2_tac >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  strip_tac >- ( rw[] >> simp[Once Cevaluate_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    qmatch_assum_rename_tac`syneq_exp c1 c2 (LENGTH env1) (LENGTH env2) V e1 e2`[] >>
    last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
    simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`s3`,`v3`] >>
    strip_tac >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`s3` >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`v3` >>
    simp[] >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    disj1_tac >>
    first_x_assum match_mp_tac >>
    metis_tac[] ) >>
  rw[] >>
  simp[Once Cevaluate_cases] >>
  fsrw_tac[DNF_ss][EXISTS_PROD] >>
  disj2_tac >>
  qmatch_assum_rename_tac`syneq_exp c1 c2 (LENGTH env1) (LENGTH env2) V e1 e2`[] >>
  last_x_assum(qspecl_then[`c2`,`V`,`s2`,`env2`,`e2`]mp_tac) >>
  simp[GSYM AND_IMP_INTRO] >> disch_then(mp_tac o UNDISCH_ALL) >>
  fsrw_tac[DNF_ss][] >>
  map_every qx_gen_tac[`s3`,`v3`] >>
  strip_tac >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`s3` >>
  CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`v3` >>
  simp[] >>
  first_x_assum match_mp_tac >>
  metis_tac[] )

(* Closed values *)

val (Cclosed_rules,Cclosed_ind,Cclosed_cases) = Hol_reln`
(Cclosed c (CLitv l)) ∧
(EVERY (Cclosed c) vs ⇒ Cclosed c (CConv cn vs)) ∧
((EVERY (Cclosed c) env) ∧
 n < LENGTH defs ∧
 (∀az b. MEM (INL (az,b)) defs ⇒
    ∀v. v ∈ free_vars b ⇒ v < az + LENGTH defs + LENGTH env) ∧
 (∀l. MEM (INR l) defs
   ⇒ l ∈ FDOM c
   ∧ ((c ' l).nz = LENGTH defs)
   ∧ ((c ' l).ez = LENGTH env)
   ∧ closed_cd (c ' l).cd)
⇒ Cclosed c (CRecClos env defs n)) ∧
(Cclosed c (CLoc m))`

val Cclosed_lit_loc = store_thm("Cclosed_lit_loc",
  ``Cclosed c (CLitv l) ∧
    Cclosed c (CLoc n)``,
  rw[Cclosed_rules])
val _ = export_rewrites["Cclosed_lit_loc"]

val doPrim2_closed = store_thm(
"doPrim2_closed",
``∀c b ty op v1 v2. every_result (Cclosed c) (doPrim2 b ty op v1 v2)``,
ntac 4 gen_tac >>
Cases >> TRY (Cases_on `l`) >>
Cases >> TRY (Cases_on `l`) >>
rw[])
val _ = export_rewrites["doPrim2_closed"];

val CevalPrim2_closed = store_thm(
"CevalPrim2_closed",
``∀c p2 v1 v2. every_result (Cclosed c) (CevalPrim2 p2 v1 v2)``,
gen_tac >> Cases >> rw[])
val _ = export_rewrites["CevalPrim2_closed"];

val CevalPrim1_closed = store_thm(
"CevalPrim1_closed",
``∀c uop s v. EVERY (Cclosed c) s ∧ Cclosed c v ⇒
  EVERY (Cclosed c) (FST (CevalPrim1 uop s v)) ∧
  every_result (Cclosed c) (SND (CevalPrim1 uop s v))``,
gen_tac >> Cases >> rw[LET_THM,Cclosed_rules] >> rw[]
>- ( Cases_on`v`>>fs[] )
>- ( Cases_on`v`>>fs[] >>
  rw[el_check_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL]))

val CevalUpd_closed = store_thm(
"CevalUpd_closed",
``(∀c s v1 v2. Cclosed c v2 ⇒ every_result (Cclosed c) (SND (CevalUpd s v1 v2))) ∧
  (∀c s v1 v2. EVERY (Cclosed c) s ∧ Cclosed c v2 ⇒
    EVERY (Cclosed c) (FST (CevalUpd s v1 v2)))``,
  conj_tac >>
  ntac 2 gen_tac >>
  Cases >> simp[] >- rw[] >>
  rpt gen_tac >> strip_tac >>
  rw[] >>
  fsrw_tac[DNF_ss][EVERY_MEM] >> rw[] >>
  imp_res_tac MEM_LUPDATE >> fs[])

val Cclosed_bundle = store_thm("Cclosed_bundle",
  ``Cclosed c (CRecClos cenv defs n) ∧ n < LENGTH defs ⇒
    ∀m. m < LENGTH defs ⇒ Cclosed c (CRecClos cenv defs m)``,
  simp[Once Cclosed_cases] >>
  simp[Once Cclosed_cases] >>
  metis_tac[])

val Cevaluate_closed = store_thm("Cevaluate_closed",
  ``(∀c s env exp res. Cevaluate c s env exp res
     ⇒ free_vars exp ⊆ count (LENGTH env)
     ∧ FEVERY (closed_cd o closure_extra_data_cd o SND) c
     ∧ EVERY (Cclosed c) env
     ∧ EVERY (Cclosed c) s
     ⇒
     EVERY (Cclosed c) (FST res) ∧
     every_result (Cclosed c) (SND res)) ∧
    (∀c s env exps ress. Cevaluate_list c s env exps ress
     ⇒ BIGUNION (IMAGE free_vars (set exps)) ⊆ count (LENGTH env)
     ∧ FEVERY (closed_cd o closure_extra_data_cd o SND) c
     ∧ EVERY (Cclosed c) env
     ∧ EVERY (Cclosed c) s
     ⇒
     EVERY (Cclosed c) (FST ress) ∧
     every_result (EVERY (Cclosed c)) (SND ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[DNF_ss][] >>
    rfs[] >>
    conj_tac >>
    first_x_assum(match_mp_tac o MP_CANON) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases >> fsrw_tac[ARITH_ss][] >>
    rw[] >> res_tac >> fs[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
  strip_tac >- ( rw[] >> rw[Once Cclosed_cases]) >>
  strip_tac >- (
    srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >> fs[] >>
    rw[Once Cclosed_cases] ) >>
  strip_tac >- (
    srw_tac[ETA_ss][FOLDL_UNION_BIGUNION] ) >>
  strip_tac >- ( rw[] >> rw[Once Cclosed_cases]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fs[] >>
    fsrw_tac[DNF_ss][Q.SPECL[`c`,`CConv m vs`] Cclosed_cases,EVERY_MEM,MEM_EL] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases >> fsrw_tac[ARITH_ss][] >>
    rw[] >> res_tac >> fs[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_FUPDATE_LIST,FOLDL_UNION_BIGUNION] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,LET_THM] >>
    conj_tac >- (
      rw[] >> res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    lrw[EVERY_REVERSE,EVERY_GENLIST] >>
    simp[Once Cclosed_cases] >>
    fsrw_tac[DNF_ss][EVERY_MEM,FEVERY_DEF] >>
    map_every qx_gen_tac[`az`,`b`,`v`] >>
    rw[] >>
    Cases_on`v<az`>>fsrw_tac[ARITH_ss][]>>
    rpt (first_x_assum(qspecl_then[`INL (az,b)`,`v-az`]mp_tac)) >>
    simp[] >> fsrw_tac[DNF_ss][] >>
    simp[GSYM FORALL_AND_THM,AND_IMP_INTRO] >>
    disch_then(qspec_then`v`mp_tac) >>
    simp[] >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once Cclosed_cases] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,PRE_SUB1] >>
    rw[] >> fsrw_tac[DNF_ss][FEVERY_DEF] >>
    Cases_on`v≤az`>>fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[FOLDL_UNION_BIGUNION] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    Cases_on`cb`>>fs[LET_THM] >- (
      PairCases_on`x`>>fs[]>>
      simp[EVERY_REVERSE,EVERY_GENLIST] >>
      reverse conj_tac >- (
        conj_tac >- metis_tac[Cclosed_bundle] >>
        fs[Once Cclosed_cases] ) >>
      fs[Once Cclosed_cases] >>
      last_x_assum(qspecl_then[`x0`,`x1`]mp_tac) >>
      `MEM (INL (x0,x1)) defs` by (rw[MEM_EL] >> PROVE_TAC[]) >>
      fsrw_tac[ARITH_ss,DNF_ss][]) >>
    fsrw_tac[DNF_ss][UNCURRY,SUBSET_DEF] >>
    simp[EVERY_REVERSE,EVERY_MAP] >>
    fsrw_tac[DNF_ss][IN_FRANGE] >>
    fsrw_tac[DNF_ss][EVERY_MEM,FEVERY_DEF] >>
    fs[(Q.SPECL[`c`,`CRecClos cenv defs d`]Cclosed_cases)] >>
    qmatch_assum_rename_tac`EL n defs = INR z`[] >>
    reverse conj_tac >- (
      conj_tac >- metis_tac[] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_EL] ) >>
    fsrw_tac[DNF_ss,ARITH_ss][closed_cd_def,MEM_EL]) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [free_vars_def,every_result_def] >>
    metis_tac[CevalPrim1_closed]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >- (
      match_mp_tac (MP_CANON (CONJUNCT2 CevalUpd_closed)) >>
      rw[]) >>
    match_mp_tac (CONJUNCT1 CevalUpd_closed) >>
    rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fs[] >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [] >>
    fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    full_simp_tac std_ss [] >>
    fs[] ) >>
  rpt gen_tac >> ntac 2 strip_tac >>
  full_simp_tac std_ss [] >>
  fs[] )

(* Cevaluate mkshift *)

val Cevaluate_mkshift = store_thm("Cevaluate_mkshift",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒
      ∀env' env0 env1 env1' f k.
        (env = env0 ++ env1) ∧ (env' = env0 ++ env1') ∧ (LENGTH env0 = k) ∧
        (∀v. k ≤ v ∧ v < LENGTH env ⇒ f(v-k) < LENGTH env1' ∧ (EL (f(v-k)) env1' = EL (v-k) env1)) ⇒
        ∃res'.
        Cevaluate c s env' (mkshift f k exp) res' ∧
        EVERY2 (syneq c c) (FST res) (FST res') ∧
        result_rel (syneq c c) (SND res) (SND res')) ∧
    (∀c s env es rs. Cevaluate_list c s env es rs ⇒
      ∀env' env0 env1 env1' f k.
        (env = env0 ++ env1) ∧ (env' = env0 ++ env1') ∧ (LENGTH env0 = k) ∧
        (∀v. k ≤ v ∧ v < LENGTH env ⇒ f(v-k) < LENGTH env1' ∧ (EL (f(v-k)) env1' = EL (v-k) env1)) ⇒
        ∃rs'.
        Cevaluate_list c s env' (MAP (mkshift f k) es) rs' ∧
        EVERY2 (syneq c c) (FST rs) (FST rs') ∧
        result_rel (EVERY2 (syneq c c)) (SND rs) (SND rs'))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    last_x_assum(qspecl_then[`env0`,`env1`,`env1'`,`f`]mp_tac) >>
    rw[] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`n`,`FST res'`] >>
    Cases_on`res'`>>fs[] >>
    first_x_assum(qspecl_then[`CLitv(IntLit n)::env0`,`env1`,`env1'`,`f`]mp_tac) >>
    simp[ADD1] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >> Cases >>
      fsrw_tac[ARITH_ss][ADD1] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    disch_then(Q.X_CHOOSE_THEN`res'`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`Cevaluate c s' env' e' res'` >>
    qspecl_then[`c`,`s'`,`env'`,`e'`,`res'`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    qmatch_assum_rename_tac`EVERY2 (syneq c c) s' ss`[] >>
    disch_then(qspecl_then[`c`,`$=`,`ss`,`env'`,`e'`]mp_tac) >>
    simp[syneq_exp_refl] >>
    metis_tac[EVERY2_syneq_trans,result_rel_syneq_trans] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    disj2_tac >>
    fsrw_tac[DNF_ss][EXISTS_PROD] ) >>
  strip_tac >- (
    rw[] >> rw[] >> fsrw_tac[ARITH_ss][] >>
    lrw[EL_APPEND1,EL_APPEND2] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss,ETA_ss][] >>
    simp[Once syneq_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss,ETA_ss][] >>
    simp[Once syneq_cases] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    fs[Once syneq_cases] >>
    fsrw_tac[DNF_ss][] >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`m` >>
    simp[] >> metis_tac[]) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] ) >>
  strip_tac >- (
    rw[Cevaluate_proj] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] >>
    fs[Once (Q.SPECL[`c`,`c`,`CConv m vs`](CONJUNCT1 syneq_cases))] >>
    fsrw_tac[DNF_ss][] >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`m` >>
    first_x_assum(qspecl_then[`env0`,`env1`,`env1'`,`f`]mp_tac) >>
    simp[] >> strip_tac >>
    qmatch_assum_rename_tac`EVERY2 (syneq c c) s' ss`[] >>
    qexists_tac`ss` >> simp[] >>
    HINT_EXISTS_TAC >> simp[] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rfs[MEM_ZIP] >>
    fsrw_tac[DNF_ss][] ) >>
  strip_tac >- (
    rw[Cevaluate_proj] >>
    fsrw_tac[DNF_ss][EXISTS_PROD] ) >>
  strip_tac >- (
    rw[] >>
    simp[Cevaluate_let] >>
    fsrw_tac[DNF_ss][] >>
    disj1_tac >>
    last_x_assum(qspecl_then[`env0`,`env1`,`env1'`,`f`]mp_tac) >>
    rw[] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`v'`,`FST res'`] >>
    Cases_on`res'`>>fs[]>>
    first_x_assum(qspecl_then[`v::env0`,`env1`,`env1'`,`f`]mp_tac) >>
    simp[ADD1] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >> Cases >>
      fsrw_tac[ARITH_ss][ADD1] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    disch_then(Q.X_CHOOSE_THEN`res'`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`Cevaluate c s' env' e' res'` >>
    qspecl_then[`c`,`s'`,`env'`,`e'`,`res'`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
    simp[] >>
    qmatch_assum_rename_tac`EVERY2 (syneq c c) s' ss`[] >>
    disch_then(qspecl_then[`c`,`$=`,`ss`,`v'::(TL env')`,`e'`]mp_tac) >>
    simp[syneq_exp_refl,Abbr`env'`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      Cases >> simp[EL_CONS] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    metis_tac[EVERY2_syneq_trans,result_rel_syneq_trans] ) >>
  strip_tac >- (
    rw[] >>
    simp[Cevaluate_let] >>
    fsrw_tac[DNF_ss][EXISTS_PROD]) >>
  strip_tac >- (
    rw[LET_THM] >>
    simp[Once Cevaluate_cases] >>
    simp[GSYM CONJ_ASSOC] >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- (
      simp[EVERY_MAP] >>
      fs[EVERY_MEM] >>
      Cases >> simp[] >>
      TRY BasicProvers.CASE_TAC >>
      rw[] >> res_tac >> fs[]


      gen_tac >> strip_tac >>
      res_tac
      fsrw_tac[][EVERY_MEM]

(* Cevaluate deterministic *)

val Cevaluate_determ = store_thm("Cevaluate_determ",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒ ∀res'. Cevaluate c s env exp res' ⇒ (res' = res)) ∧
    (∀c s env exps ress. Cevaluate_list c s env exps ress ⇒ ∀ress'. Cevaluate_list c s env exps ress' ⇒ (ress' = ress))``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    TRY(Cases_on`res'`)>>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][FORALL_PROD] >>
    res_tac >> fs[] >>
    rw[] >> fs[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[Cevaluate_con] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_con] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_proj] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_proj] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_let] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[Cevaluate_let] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once Cevaluate_cases] >>
    fsrw_tac[DNF_ss][] >>
    Cases_on`cb`>|[Cases_on`x`,ALL_TAC]>>fs[UNCURRY]>>
    rw[] >>
    res_tac >> fs[] >> rw[] >> rfs[] >> rw[] >>
    res_tac >> fs[] >> rw[] >>
    fs[LET_THM,UNCURRY]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[] >> rw[] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[]) >>
  strip_tac >- rw[Once Cevaluate_cases] >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[] >> rw[] >>
    res_tac >> fs[] ) >>
  strip_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once Cevaluate_cases] >>
    res_tac >> fs[] >> rw[] ) >>
  rw[] >>
  pop_assum mp_tac >>
  rw[Once Cevaluate_cases] >>
  res_tac >> fs[] >> rw[] >>
  res_tac >> fs[])

val _ = export_theory()
