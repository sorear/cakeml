(*Generated by Lem from semantics/ast.lem.*)
open bossLib Theory Parse res_quanTheory
open finite_mapTheory listTheory pairTheory pred_setTheory integerTheory
open set_relationTheory sortingTheory stringTheory wordsTheory

val _ = numLib.prefer_num();

val _ = new_theory "Ast"

open MiniMLTheory TokensTheory

(* An AST that can be the result of parsing, and then elaborated into the type
 * annotated AST in miniML.lem.  We are assuming that constructors start with
 * capital letters, and non-constructors start with lower case (as in OCaml) so
 * that the parser can determine what is a constructor application.  Example
 * syntax in comments before each node.
 * 
 * Also, an elaboration from this syntax to the AST in miniML.lem.  The only
 * job of the elaboration is to spot variables and types that are bound to ML
 * primitives.  The elaboration isn't particularly sophisticated: primitives
 * are always turned into functions, and we don't look for places where the
 * primitive is already applied, so 1 + 2 becomes (fun x y -> x + y) 1 2 
 *)

(*open MiniML*)

val _ = Hol_datatype `
 ast_pat =
    (* x *)
    Ast_Pvar of varN
    (* 1 *)
    (* true *)
    (* () *)
  | Ast_Plit of lit
    (* C(x,y) *)
    (* D *)
    (* E x *)
  | Ast_Pcon of conN => ast_pat list
    (* ref x *)
  | Ast_Pref of ast_pat`;


val _ = Hol_datatype `
 ast_exp =
    (* raise 4 *)
    Ast_Raise of error
    (* e handle x => e *)
  | Ast_Handle of ast_exp => varN => ast_exp
    (* 1 *)
    (* true *)
    (* () *)
  | Ast_Lit of lit
    (* x *)
  | Ast_Var of varN
    (* C(x,y) *)
    (* D *)
    (* E x *)
  | Ast_Con of conN => ast_exp list
    (* fn x => e *)
  | Ast_Fun of varN => ast_exp
    (* e e *)
  | Ast_App of ast_exp => ast_exp
    (* e andalso e *)
    (* e orelse e *)
  | Ast_Log of log => ast_exp => ast_exp
    (* if e then e else e *)
  | Ast_If of ast_exp => ast_exp => ast_exp
    (* case e of C(x,y) => x | D y => y *)
  | Ast_Mat of ast_exp => (ast_pat # ast_exp) list
    (* let val x = e in e end *)
  | Ast_Let of varN => ast_exp => ast_exp
    (* let fun f x = e and g y = e in e end *) 
  | Ast_Letrec of (varN # varN # ast_exp) list => ast_exp`;


val _ = Hol_datatype `
 ast_t =
    (* 'a *)
    Ast_Tvar of tvarN
    (* t *)
    (* num t *)
    (* (num,bool) t *)
  | Ast_Tapp of ast_t list => typeN
    (* t -> t *)
  | Ast_Tfn of ast_t => ast_t`;


(* type t = C of t1 * t2 | D of t2  * t3
 * and 'a u = E of 'a
 * and ('a,'b) v = F of 'b u | G of 'a u *)
val _ = type_abbrev( "ast_type_def" , ``: ( tvarN list # typeN # (conN # ast_t list) list) list``);

val _ = Hol_datatype `
 ast_dec =
    (* val (C(x,y)) = C(1,2) *) 
    Ast_Dlet of ast_pat => ast_exp
    (* fun f x = e and g y = f *) 
  | Ast_Dletrec of (varN # varN # ast_exp) list
    (* see above *)
  | Ast_Dtype of ast_type_def`;


val _ = type_abbrev( "ast_decs" , ``: ast_dec list``);

val _ = Hol_datatype `
 ast_spec =
    Ast_Sval of ast_t
  | Ast_Stype of ast_type_def
  | Ast_Stype_opq of typeN`;


val _ = type_abbrev( "ast_specs" , ``: ast_spec list``);

val _ = Hol_datatype `
 ast_top =
    Ast_Tmodule of mvarN => ast_specs => ast_decs
  | Ast_Tdec of ast_dec`;


val _ = type_abbrev( "ast_prog" , ``: ast_top list``);


(*val elab_p : ast_pat -> pat unit*) 
 val elab_p_defn = Hol_defn "elab_p" `

(elab_p (Ast_Pvar n) = Pvar n NONE)
/\
(elab_p (Ast_Plit l) = Plit l)
/\
(elab_p (Ast_Pcon cn ps) = Pcon cn (elab_ps ps))
/\
(elab_p (Ast_Pref p) = Pref (elab_p p))
/\
(elab_ps [] = [])
/\
(elab_ps (p::ps) = elab_p p :: elab_ps ps)`;

val _ = Defn.save_defn elab_p_defn;

val _ = Hol_datatype `
 ops =
    Is_uop of uop
  | Is_op of op
  | Isnt`;


(*val get_op : varN -> ops*)
val _ = Define `
 (get_op n =
  (case n of
      "+" =>
      Is_op (Opn Plus)
    | "-" =>
      Is_op (Opn Minus)
    | "*" =>
      Is_op (Opn Times)
    | "div" =>
      Is_op (Opn Divide)
    | "mod" =>
      Is_op (Opn Modulo)
    | "<" =>
      Is_op (Opb Lt)
    | ">" =>
      Is_op (Opb Gt)
    | "<=" =>
      Is_op (Opb Leq)
    | ">=" =>
      Is_op (Opb Geq)
    | "=" =>
      Is_op Equality
    | ":=" =>
      Is_op Opassign
    | "!" =>
      Is_uop Opderef
    | "ref" =>
      Is_uop Opref
    | _ =>
      Isnt
  ))`;


(*val elab_t : list varN -> ast_t -> t*)
(*val elab_e : list varN -> ast_exp -> exp unit*)
(*val elab_funs : list varN -> list (varN * varN * ast_exp) -> 
                list (varN *option unit * varN *option unit * exp unit)*)
(*val elab_dec : list typeN -> list varN -> ast_dec -> list typeN * list varN * dec unit*)
(*val elab_decs : list typeN -> list varN -> list ast_dec -> list typeN * list varN * list (dec unit)*)

 val elab_e_defn = Hol_defn "elab_e" `

(elab_e bound (Ast_Raise err) =
  Raise err)
/\
(elab_e bound (Ast_Handle e1 x e2) =
  Handle (elab_e bound e1) x (elab_e (x::bound) e2))
/\
(elab_e bound (Ast_Lit l) =
  Lit l)
/\ (elab_e bound (Ast_Var n) =
  if MEM n bound then
    Var n NONE
  else
    (case get_op n of
        Isnt => Var n NONE
      | Is_op op =>
          Fun "x" NONE (Fun "y" NONE (App op (Var "x" NONE) (Var "y" NONE)))
      | Is_uop uop =>
          Fun "x" NONE (Uapp uop (Var "x" NONE))
    ))
/\ 
(elab_e bound (Ast_Con cn es) =
  Con cn (MAP (elab_e bound) es))
/\
(elab_e bound (Ast_Fun n e) =
  Fun n NONE (elab_e (n::bound) e))
/\
(elab_e bound (Ast_App e1 e2) =
  App Opapp (elab_e bound e1) (elab_e bound e2))
/\
(elab_e bound (Ast_Log log e1 e2) =
  Log log (elab_e bound e1) (elab_e bound e2))
/\
(elab_e bound (Ast_If e1 e2 e3) =
  If (elab_e bound e1) (elab_e bound e2) (elab_e bound e3))
/\
(elab_e bound (Ast_Mat e pes) =
  Mat (elab_e bound e) 
      (MAP (\ (p,e) . 
                   let p' = elab_p p in
                     (p', elab_e (pat_bindings p' bound) e))
                pes)) 
/\
(elab_e bound (Ast_Let x e1 e2) =
  Let NONE x NONE (elab_e bound e1) (elab_e (x::bound) e2))
/\
(elab_e bound (Ast_Letrec funs e) =
  Letrec NONE (elab_funs ((MAP (\ (n1,n2,e) . n1) funs) ++ bound) funs) 
              (elab_e bound e))
/\
(elab_funs bound [] =
  [])
/\
(elab_funs bound ((n1,n2,e)::funs) =
  (n1,NONE,n2,NONE,elab_e (n2::bound) e) :: elab_funs bound funs)`;

val _ = Defn.save_defn elab_e_defn;

 val get_prim_type_defn = Hol_defn "get_prim_type" `
 (get_prim_type tn =
  (case tn of
      "int" => SOME TC_int
    | "bool" => SOME TC_bool
    | "unit" => SOME TC_unit
    | "ref" => SOME TC_ref
    | _ => NONE
  ))`;

val _ = Defn.save_defn get_prim_type_defn;

 val elab_t_defn = Hol_defn "elab_t" `

(elab_t type_bound (Ast_Tvar n) = Tvar n)
/\
(elab_t type_bound (Ast_Tfn t1 t2) =
  Tfn (elab_t type_bound t1) (elab_t type_bound t2))
/\
(elab_t type_bound (Ast_Tapp ts tn) =
  let ts' = MAP (elab_t type_bound) ts in
    if MEM tn type_bound then
      Tapp ts' (TC_name tn)
    else 
      (case get_prim_type tn of
          NONE => Tapp ts' (TC_name tn)
        | SOME tc0 => Tapp ts' tc0
      ))`;

val _ = Defn.save_defn elab_t_defn;

 val elab_dec_defn = Hol_defn "elab_dec" `

(elab_dec type_bound bound (Ast_Dlet p e) =
  let p' = elab_p p in
    (type_bound, pat_bindings p' bound, Dlet NONE p' (elab_e bound e)))
/\
(elab_dec type_bound bound (Ast_Dletrec funs) =
  let bound' = (MAP (\ (n1,n2,e) . n1) funs) ++ bound in
    (type_bound, bound', Dletrec NONE (elab_funs bound' funs)))
/\
(elab_dec type_bound bound (Ast_Dtype t) = 
  let type_bound' = MAP (\ (tvs,tn,ctors) . tn) t ++ type_bound in
  (type_bound',
   bound, 
   Dtype (MAP (\ (tvs,tn,ctors) . 
                     (tvs, tn, MAP (\ (cn,t) . (cn, MAP (elab_t type_bound) t)) ctors))
                   t)))`;

val _ = Defn.save_defn elab_dec_defn;

 val elab_decs_defn = Hol_defn "elab_decs" `

(elab_decs type_bound bound [] = (type_bound, bound, []))
/\
(elab_decs type_bound bound (d::ds) = 
  let (type_bound', bound', d') = elab_dec type_bound bound d in
  let (type_bound'', bound'', ds') = elab_decs type_bound' bound' ds in
    (type_bound'', bound'', d'::ds'))`;

val _ = Defn.save_defn elab_decs_defn;
val _ = export_theory()

