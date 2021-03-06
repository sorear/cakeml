(*Generated by Lem from ffi.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory lem_pervasives_extraTheory libTheory;

val _ = numLib.prefer_num();



val _ = new_theory "ffi"

(*
  An oracle says how to perform an ffi call based on its internal
  state, represented by the type variable 'ffi.
*)
(*open import Pervasives*)
(*open import Pervasives_extra*)
(*open import Lib*)


val _ = Hol_datatype `
 ffi_outcome = FFI_failed | FFI_diverged`;


val _ = Hol_datatype `
 oracle_result = Oracle_return of 'ffi => word8 list | Oracle_final of ffi_outcome`;

val _ = type_abbrev((*  'ffi *) "oracle_function" , ``: 'ffi -> word8 list -> word8 list -> 'ffi oracle_result``);
val _ = type_abbrev((*  'ffi *) "oracle" , ``: string -> 'ffi oracle_function``);

(* An I/O event, IO_event s bytes bytes2, represents the call of FFI function s with
* immutable input bytes and mutable input map fst bytes2,
* returning map snd bytes2 in the mutable array. *)

val _ = Hol_datatype `
 io_event = IO_event of string => word8 list => ( (word8 # word8)list)`;


val _ = Hol_datatype `
 final_event = Final_event of string => word8 list => word8 list => ffi_outcome`;


val _ = Hol_datatype `
(*  'ffi *) ffi_state =
<| oracle      : 'ffi oracle
 ; ffi_state   : 'ffi
 ; io_events   : io_event list
 |>`;


(*val initial_ffi_state : forall 'ffi. oracle 'ffi -> 'ffi -> ffi_state 'ffi*)
val _ = Define `
 ((initial_ffi_state:(string -> 'ffi oracle_function) -> 'ffi -> 'ffi ffi_state) oc ffi=
 (<| oracle      := oc
 ; ffi_state   := ffi
 ; io_events   := ([])
 |>))`;


val _ = Hol_datatype `
 ffi_result = FFI_return of 'ffi ffi_state => word8 list | FFI_final of final_event`;


(*val call_FFI : forall 'ffi. ffi_state 'ffi -> string -> list word8 -> list word8 -> ffi_result 'ffi*)
val _ = Define `
 ((call_FFI:'ffi ffi_state -> string ->(word8)list ->(word8)list -> 'ffi ffi_result) st s conf bytes=
   (if ~ (s = "") then
    (case st.oracle s st.ffi_state conf bytes of
      Oracle_return ffi' bytes' =>
        if LENGTH bytes' = LENGTH bytes then
          (FFI_return
            ( st with<| ffi_state := ffi'
                    ; io_events :=
                        (st.io_events ++
                          [IO_event s conf (ZIP (bytes, bytes'))])
            |>)
            bytes')
        else FFI_final(Final_event s conf bytes FFI_failed)
    | Oracle_final outcome =>
          FFI_final(Final_event s conf bytes outcome)
    )
  else FFI_return st bytes))`;


val _ = Hol_datatype `
 outcome = Success | Resource_limit_hit | FFI_outcome of final_event`;


(* A program can Diverge, Terminate, or Fail. We prove that Fail is
   avoided. For Diverge and Terminate, we keep track of what I/O
   events are valid I/O events for this behaviour. *)
val _ = Hol_datatype `
 behaviour =
    (* There cannot be any non-returning FFI calls in a diverging
       exeuction. The list of I/O events can be finite or infinite,
       hence the llist (lazy list) type. *)
    Diverge of  io_event llist
    (* Terminating executions can only perform a finite number of
       FFI calls. The execution can be terminated by a non-returning
       FFI call. *)
  | Terminate of outcome => io_event list
    (* Failure is a behaviour which we prove cannot occur for any
       well-typed program. *)
  | Fail`;


(* trace-based semantics can be recovered as an instance of oracle-based
 * semantics as follows. *)

(*val trace_oracle : oracle (llist io_event)*)
val _ = Define `
 ((trace_oracle:string ->(io_event)llist ->(word8)list ->(word8)list ->((io_event)llist)oracle_result) s io_trace conf input=
   ((case LHD io_trace of
    SOME (IO_event s' conf' bytes2) =>
      if (s = s') /\ (MAP FST bytes2 = input) /\ (conf = conf') then
        Oracle_return (THE (LTL io_trace)) (MAP SND bytes2)
      else Oracle_final FFI_failed
  | _ => Oracle_final FFI_failed
  )))`;

val _ = export_theory()

