(*
  The CakeML program implementing the word frequency application.
  This is produced by a combination of translation and CF verification.
*)

open preamble
     ml_translatorLib cfTacticsLib basisFunctionsLib cfLetAutoLib
     ioProgLib basisProgTheory
     mlstringTheory balanced_mapTheory splitwordsTheory

(* TODO: simplify the required includes (translator, basis, CF) for such examples *)

val _ = new_theory "wordfreqProg";

val _ = translation_extends"basisProg";

(* Avoid printing potentially very long output *)
val _ = Globals.max_print_depth := 20

(* Pure functions for word frequency counting *)

val lookup0_def = Define`
  lookup0 w t = case lookup compare w t of NONE => 0n | SOME n => n`;

val lookup0_empty = Q.store_thm("lookup0_empty[simp]",
  `lookup0 w empty = 0`, EVAL_TAC);

val insert_word_def = Define`
  insert_word t w =
    insert compare w (lookup0 w t + 1) t`;

val insert_line_def = Define`
  insert_line t s =
     FOLDL insert_word t (tokens isSpace s)`;

(* and their verification *)

val key_set_compare_unique = Q.store_thm("key_set_compare_unique[simp]",
  `key_set compare k = {k}`,
  rw[key_set_def,EXTENSION] \\
  metis_tac[TotOrd_compare,totoTheory.TotOrd]);

val IMAGE_key_set_compare_inj = Q.store_thm("IMAGE_key_set_compare_inj[simp]",
  `IMAGE (key_set compare) s1 = IMAGE (key_set compare) s2 ⇔ s1 = s2`,
  rw[EQ_IMP_THM]
  \\ fs[Once EXTENSION]
  \\ fs[EQ_IMP_THM] \\ rw[]
  \\ res_tac \\ fs[]);

val lookup0_insert = Q.store_thm("lookup0_insert",
  `invariant compare t ⇒
   lookup0 k (insert compare k' v t) =
   if k = k' then v else lookup0 k t`,
  rw[lookup0_def,lookup_insert,good_cmp_compare] \\
  metis_tac[TotOrd_compare,totoTheory.TotOrd]);

val insert_line_thm = Q.store_thm("insert_line_thm",
  `invariant compare t ∧
   insert_line t s = t'
   ⇒
   invariant compare t' ∧
   (∀w. lookup0 w t' =
        lookup0 w t + frequency s w) ∧
   FDOM (to_fmap compare t') = FDOM (to_fmap compare t) ∪ (IMAGE (key_set compare) (set (splitwords s)))`,
  strip_tac \\ rveq \\
  simp[insert_line_def,splitwords_def,frequency_def] \\
  Q.SPEC_TAC(`tokens isSpace s`,`ls`) \\
  ho_match_mp_tac SNOC_INDUCT \\ simp[] \\
  ntac 3 strip_tac \\
  simp[MAP_SNOC,FOLDL_SNOC,insert_word_def] \\
  rw[good_cmp_compare,insert_thm,FILTER_SNOC,lookup0_insert] \\
  rw[EXTENSION] \\ metis_tac[]);

val FOLDL_insert_line = Q.store_thm("FOLDL_insert_line",
  `∀ls t t' s.
    invariant compare t ∧ t' = FOLDL insert_line t ls ∧
    EVERY (λw. ∃x. w = strcat x (strlit "\n")) ls ∧
    s = concat ls
    ⇒
    invariant compare t' ∧
    (∀w. lookup0 w t' = lookup0 w t + frequency s w) ∧
    FDOM (to_fmap compare t') = FDOM (to_fmap compare t) ∪ IMAGE (key_set compare) (set (splitwords s))`,
  Induct \\ simp[concat_def] \\ ntac 3 strip_tac \\
  rename1`insert_line t w` \\
  imp_res_tac insert_line_thm \\ fs[] \\
  `strlit "\n" = str #"\n"` by EVAL_TAC \\
  `isSpace #"\n"` by EVAL_TAC \\
  first_x_assum drule \\
  rw[frequency_concat,splitwords_concat,frequency_concat_space,splitwords_concat_space] \\
  rw[EXTENSION] \\ metis_tac[]);

(* TODO:
  given that this is also used in grep,
  should we include it in the basis? *)

val res = translate lookup_def;
val res = translate singleton_def;
val res = translate ratio_def;
val res = translate size_def;
val res = translate delta_def;
val _ = next_ml_names := ["balanceL","balanceR"];
val res = translate balanceL_def;
val res = translate balanceR_def;
val res = translate insert_def;
val res = translate empty_def;
val _ = next_ml_names := ["foldrWithKey","toAscList"];
val res = translate foldrWithKey_def;
val res = translate toAscList_def;

val res = translate lookup0_def;
val res = translate insert_word_def;
val res = translate insert_line_def;

(* TODO: possible extension: pad the word so the colons will line up *)
val format_output_def = Define`
  format_output (k,v) = concat [k; strlit": "; toString (&v); strlit"\n"]`;
val res = translate format_output_def;

(* TODO: explain process_topdecs, CakeML syntax etc.
         but actually this should be covered by the wordcount example *)

(* TODO: do something like this as an exercise?

(* An imperative higher-order function for applying a function to every element
   in a bst in order *)

val app_in_order = process_topdecs`
  fun app_in_order f t =
  case t of
    Tip => ()
  | Bin (_,k,v,l,r) =>
      (f k v; app_in_order f l; app_in_order f r)`;
val () = append_prog app_in_order;

(*
val app_in_order_spec = Q.store_thm("app_in_order_spec",
  `BALANCED_MAP_BALANCED_MAP_TYPE kty vty t tv ∧
   (∀n kv vv.
      n < LENGTH (toAscList t) ∧
      kty (FST (EL n (toAscList t))) kv ∧
      vty (SND (EL n (toAscList t))) vv
      ⇒
        app p fv [kv; vv] (P (TAKE n (toAscList t)))
          (POSTv uv. &UNIT_TYPE () uv * P (TAKE (n+1) (toAscList t))))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"app_in_order"(get_ml_prog_state())) [fv; tv]
     (P [])
     (POSTv uv. &UNIT_TYPE () uv *
                P (toAscList t))`,
  rw[] \\
  Induct_on`t`
*)

*)

(* TODO: how do you debug a definition like this that fails to process?
I tried processing one internal declaration at a time (deleting the others)
val wordfreq = process_topdecs`
  fun wordfreq _ =
    let
      val filename = List.hd (Commandline.arguments())
      val fd = FileIO.openIn filename
      fun loop t =
        case FileIO.inputLine fd of NONE => t
           | SOME line => insert_line t line
      val t = loop empty
      val _ = FileIO.close fd
      fun print_output k v = print (format_output k v)
    in
      app_in_order print_output t
    end`;

n.b. this is extra hard with missing/invalid definitions (like "empty" and
"toAscList", which were not originally translated) so that even if it  parses it
might lead to bad CF errors later
*)

val wordfreq = process_topdecs`
  fun wordfreq u =
    case FileIO.inputLinesFrom (List.hd (Commandline.arguments()))
    of SOME lines =>
      print_list
        (List.map format_output
          (toAscList
            (List.foldl insert_line empty lines)))`;

val () = append_prog wordfreq;

(* Now we state and prove a correctness theorem for the wordfreq program *)

val st = get_ml_prog_state();

(* TODO: this is wrong (because splitwords gives duplicates)
   leave it as an exercises to see why this spec is wrong?
val valid_wordfreq_output_def = Define`
  valid_wordfreq_output file_contents output =
    ∃ls. PERM ls (splitwords file_contents) ∧ SORTED $<= ls ∧
         output = FLAT (MAP (λw. explode (format_output (w, frequency file_contents w))) ls)`;
*)

val valid_wordfreq_output_def = Define`
  valid_wordfreq_output file_contents output =
    ∃ws. set ws = set (splitwords file_contents) ∧ SORTED $< ws ∧
         output = FLAT (MAP (λw. explode (format_output (w, frequency file_contents w))) ws)`;

val valid_wordfreq_output_unique = Q.store_thm("valid_wordfreq_output_unique",
  `∀out1 out2. valid_wordfreq_output s out1 ∧ valid_wordfreq_output s out2 ⇒ out1 = out2`,
  rw[valid_wordfreq_output_def] \\
  rpt AP_TERM_TAC \\
  match_mp_tac (MP_CANON SORTED_PERM_EQ) \\
  instantiate \\
  conj_asm1_tac >- (
    simp[transitive_def,antisymmetric_def] \\
    metis_tac[mlstring_lt_trans, mlstring_lt_antisym]) \\
  `ALL_DISTINCT ws ∧ ALL_DISTINCT ws'` by (
    conj_tac \\ match_mp_tac (GEN_ALL(MP_CANON SORTED_ALL_DISTINCT)) \\
    instantiate \\ simp[irreflexive_def] \\
    metis_tac[mlstring_lt_nonrefl] ) \\
  fs[ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] \\
  metis_tac[PERM_TRANS,PERM_SYM]);

val valid_wordfreq_output_exists = Q.store_thm("valid_wordfreq_output_exists",
  `∃output. valid_wordfreq_output (implode file_chars) output`,
  rw[valid_wordfreq_output_def] \\
  qexists_tac`QSORT $<= (nub (splitwords (implode file_chars)))` \\
  qmatch_goalsub_abbrev_tac`set l1 = LIST_TO_SET l2` \\
  `PERM (nub l2) l1` by metis_tac[QSORT_PERM] \\
  imp_res_tac PERM_LIST_TO_SET \\ fs[] \\
  simp[Abbr`l1`] \\
  match_mp_tac (MP_CANON ALL_DISTINCT_SORTED_WEAKEN) \\
  qexists_tac`$<=` \\ fs[mlstring_le_thm] \\
  conj_tac >- metis_tac[ALL_DISTINCT_PERM,all_distinct_nub] \\
  match_mp_tac QSORT_SORTED \\
  simp[transitive_def,total_def] \\
  metis_tac[mlstring_lt_trans,mlstring_lt_cases]);

val wordfreq_output_spec_def =
  new_specification("wordfreq_output_spec_def",["wordfreq_output_spec"],
    GEN_ALL valid_wordfreq_output_exists |> SIMP_RULE std_ss [SKOLEM_THM]);

(* TODO: explain p:'ffi ffi_proj, or make it simpler *)
(* TODO: explain antiquotation (^) *)

val wordfreq_output_spec_unique = Q.store_thm("wordfreq_output_spec_unique",
  `valid_wordfreq_output (implode file_chars) output ⇒
   output = wordfreq_output_spec file_chars`,
   metis_tac[wordfreq_output_spec_def,valid_wordfreq_output_unique]);

val wordfreq_output_valid = Q.store_thm("wordfreq_output_valid",
  `valid_wordfreq_output (implode (THE (ALOOKUP fs.files fname)))
      (FLAT (MAP explode (MAP format_output (toAscList (FOLDL insert_line empty (all_lines fs fname))))))`,
  rw[valid_wordfreq_output_def] \\
  qmatch_goalsub_abbrev_tac`MAP format_output ls` \\
  qexists_tac `MAP FST ls` \\
  (* Now we use the theorem about insert_line proved earlier *)
  qspecl_then[`all_lines fs fname`,`empty`]mp_tac FOLDL_insert_line \\
  simp[empty_thm] \\
  impl_tac >- (
    simp[mlfileioProgTheory.all_lines_def,EVERY_MAP,implode_def,strcat_def] \\
    simp[EVERY_MEM] \\ metis_tac[explode_implode] ) \\
  strip_tac \\
  assume_tac good_cmp_compare \\ simp[Abbr`ls`] \\
  (* simplify the remaining goal using properties of toAscList etc. *)
  simp[MAP_FST_toAscList,mlstring_lt_def] \\
  simp[MAP_MAP_o,o_DEF] \\
  imp_res_tac MAP_FST_toAscList \\ fs[empty_thm] \\
  qmatch_goalsub_abbrev_tac`set (splitwords w1) = set (splitwords w2)` \\
  `splitwords w1 = splitwords w2` by (
    strip_assume_tac mlfileioProgTheory.concat_all_lines
    \\ simp[Abbr`w1`,Abbr`w2`]
    \\ `isSpace #"\n"` by EVAL_TAC
    \\ simp[splitwords_concat_space] ) \\
  simp[] \\
  AP_TERM_TAC \\
  simp[MAP_EQ_f] \\
  simp[FORALL_PROD] \\ rw[] \\
  imp_res_tac MEM_toAscList \\
  rfs[GSYM lookup_thm] \\
  rename1`lookup _ k _` \\
  first_x_assum(qspec_then`k`mp_tac) \\
  rw[lookup0_def,frequency_def]);

(* These will be needed for xlet_auto to handle our use of List.foldl *)
val insert_line_v_thm = theorem"insert_line_v_thm";
val empty_v_thm = theorem"empty_v_thm" |> Q.GENL[`a`,`b`] |> Q.ISPECL[`NUM`,`STRING_TYPE`];
(* and this for our use of List.map *)
val format_output_v_thm = theorem"format_output_v_thm";

val wordfreq_spec = Q.store_thm("wordfreq_spec",
  `hasFreeFD fs ∧ inFS_fname fs fname ∧ cl = [explode pname; explode fname]
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "wordfreq" st) [Conv NONE []]
     (COMMANDLINE cl * ROFS fs * STDOUT out)
     (POSTv uv.
       &UNIT_TYPE () uv *
       COMMANDLINE cl * ROFS fs * STDOUT (out ++ wordfreq_output_spec (THE (ALOOKUP fs.files fname))))`,
  strip_tac \\
  xcf"wordfreq" st \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull \\ rfs[]) \\
  xlet_auto >- (
    xsimpl \\
    rfs[mlfileioProgTheory.FILENAME_def,
        mlcommandLineProgTheory.wfcl_def,
        commandLineFFITheory.validArg_def,
        LENGTH_explode,EVERY_MEM] ) \\
  xmatch \\
  fs[ml_translatorTheory.OPTION_TYPE_def] \\
  reverse conj_tac >- (EVAL_TAC \\ simp[]) \\
  (* try xlet_auto to see that these specs are needed *)
  assume_tac insert_line_v_thm \\
  assume_tac empty_v_thm \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  (* try xlet_auto to see that these specs are needed *)
  assume_tac format_output_v_thm \\
  xlet_auto >- xsimpl \\
  xapp \\ xsimpl \\ instantiate \\
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`out` \\
  xsimpl \\

  qmatch_abbrev_tac`STDOUT xxxx ==>> STDOUT yyyy * GC` \\
  `xxxx = yyyy` suffices_by xsimpl \\
  map_every qunabbrev_tac[`xxxx`,`yyyy`] \\ simp[] \\

  match_mp_tac wordfreq_output_spec_unique \\
  metis_tac[wordfreq_output_valid]);

(* partial old version without help from inputLinesFrom

val wordfreq = process_topdecs`
  fun wordfreq u =
    let
      val filename = List.hd (Commandline.arguments())
      val fd = FileIO.openIn filename
      fun loop t =
        case FileIO.inputLine fd of NONE => t
           | SOME line => insert_line t line
      val t = loop empty
      val u = FileIO.close fd
    in
      List.app (print o format_output) (toAscList t)
    end`;

(* TODO:
   this is the spec I originally devised, but it doesn't work with ioProgLib.call_thm
   could ioProgLib.call_thm be made more robust for that?
   (but note since this isn't proved, it is probably wrong)
val wordfreq_spec = Q.store_thm("wordfreq_spec",
  `EVERY validArg cl ∧
   LENGTH cl > 1 ∧ SUM (MAP LENGTH cl) + LENGTH cl < 257 ∧
   fname = implode (EL 1 cl) ∧
   inFS_fname fs fname ∧
   wfFS fs
   ⇒ app (p:'ffi ffi_proj) ^(fetch_v "wordfreq" st) [Conv NONE []]
       (COMMANDLINE cl * ROFS fs * STDOUT out)
       (POSTv uv.
        &UNIT_TYPE () uv * COMMANDLINE cl * ROFS fs *
        (SEP_EXISTS out'.
           STDOUT (out ++ out') *
           &valid_wordfreq_output (THE (ALOOKUP fs.files fname)) out'))`,
  strip_tac \\
  xcf "wordfreq" st \\
  cheat);
*)

val wordfreq_spec = Q.store_thm("wordfreq_spec",
  `inFS_fname fs fname ∧ cl = MAP explode [pname; fname] ∧
   wfFS fs ∧ CARD (set (MAP FST fs.infds)) < 255 (* TODO: this should be part of wfFS *)
   ⇒ app (p:'ffi ffi_proj) ^(fetch_v "wordfreq" st) [Conv NONE []]
       (* TODO: Magnus suggests wfFS should be part of ROFS *)
       (COMMANDLINE cl * ROFS fs * STDOUT out * STDERR err)
       (POSTv uv.
        &UNIT_TYPE () uv *
        (SEP_EXISTS out' err'.
           &(∃ls.
               out' = out ++ ls ∧
               valid_wordfreq_output
                 (implode (THE (ALOOKUP fs.files fname))) ls ∧
               err' = err) *
           STDOUT out' * STDERR err') *
        (COMMANDLINE cl * ROFS fs))`,
  strip_tac \\
  xcf "wordfreq" st \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  (* try xlet_auto to see what is needed *)
  reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull \\ rfs[]) \\
  `[fname] <> []` by (rfs[]) \\
  xlet_auto >- xsimpl \\
  (* try xlet_auto to see what is needed *)
  rename1`STRING_TYPE fname fv` \\
  `FILENAME fname fv`
    by rfs[mlfileioProgTheory.FILENAME_def,
           mlcommandLineProgTheory.wfcl_def,
           mlstringTheory.LENGTH_explode,
           commandLineFFITheory.validArg_def,EVERY_MEM] \\
  xlet_auto
  >- xsimpl
  >- (xsimpl \\ rw[]) \\
  xfun_spec`loop`
    `∀t tv fd fs fdv.
      validFD fd fs ∧ WORD ((n2w fd):word64) fdv ∧
      BALANCED_MAP_BALANCED_MAP_TYPE STRING_TYPE NUM t tv ∧
      invariant compare t
      ⇒
      app p loop [tv] (ROFS fs) (POSTv tv'.
        &(∃t'. BALANCED_MAP_BALANCED_MAP_TYPE STRING_TYPE NUM t' tv' ∧ invariant compare t' ∧
               (∀w. lookup0 w t' = lookup0 w t + SUM (MAP (λln. frequency (implode ln) w) (linesFD fd fs))))
        * ROFS (bumpAllFD fd fs))`
  >- (
    Induct_on`linesFD fd fs`
    >- (
      rpt gen_tac \\
      disch_then(assume_tac o SYM) \\
      fs[GSYM rofsFFITheory.FDline_NONE_linesFD] \\
      rw[] \\ first_x_assum match_mp_tac \\
      qpat_x_assum`WORD (n2w (nextFD _)) _`kall_tac \\
      `validFD (w2n ((n2w fd):word64)) fs'` by fs[w2n_n2w,WORD_def]

      qhdtm_x_assum`WORD`kall_tac \\
      `∃fdv. WORD ((n2w fd):word64) fdv` by ( simp[WORD_def] ) \\
      m``w2n (n2w _)``
      xlet_auto

      >- (
        xsimpl
        f"nextfd"
        f"inputline"
  cheat);
*)

val spec = wordfreq_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "wordfreq"
val (sem_thm,prog_tm) = ioProgLib.call_thm (get_ml_prog_state ()) name spec
val wordfreq_prog_def = Define `wordfreq_prog = ^prog_tm`;

(* TODO:
  want a way to print this program out as concrete syntax (to be fed
  into the bootstrapped compiler for example) *)

val wordfreq_semantics =
  sem_thm
  |> ONCE_REWRITE_RULE[GSYM wordfreq_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[rofsFFITheory.wfFS_def,rofsFFITheory.inFS_fname_def,PULL_EXISTS]
  |> Q.GEN`cls`
  |> SIMP_RULE(srw_ss())[mlcommandLineProgTheory.wfcl_def,AND_IMP_INTRO,GSYM CONJ_ASSOC,LENGTH_explode]
  |> curry save_thm "wordfreq_semantics";

val _ = export_theory();