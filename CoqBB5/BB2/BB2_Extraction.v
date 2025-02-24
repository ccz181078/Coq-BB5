From CoqBB2 Require Import TNF.
From CoqBB2 Require Import BB2_Statement.
From CoqBB2 Require Import BB2_Deciders_Generic.
From CoqBB2 Require Import BB2_Deciders_Pipeline.
From CoqBB2 Require Import BB2_TNF_Enumeration.

Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatBigInt ExtrOcamlString.

(* Opposite to makeTM, transforms TMs to more convenient representation such as "BR0 BL0 BL1 BR1 AR1 AL0 AL1 None". *)
Definition unmakeTM : TM Σ ->
                      (option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ)) :=
  fun f =>
    (f St0 Σ0, f St0 Σ1, f St1 Σ0, f St1 Σ1 ).

Require Import String.
Open Scope string.

(** The following "ToString" functions allow to transform TM objects to bbchallenge's official TM string format,
see https://discuss.bbchallenge.org/t/standard-tm-text-format/60.

e.g. 1RB1LE_0LC0RE_1LD1LD_1LA---_0RB0LD
**)
Definition outToString : Σ -> string :=
  fun s => match s with
        | Σ0 => "0"
        | Σ1 => "1"
        end.

Definition dirToString : Dir -> string :=
  fun s => match s with
           | Dpos => "R"
           | Dneg => "L"
           end.

Definition stateToString : St -> string :=
  fun s => match s with
        | St0 => "A" | St1 => "B"
        end.


Definition transToString : option (Trans Σ) -> string :=
  fun o =>
    match o with
    | None => "---"
    | Some (Build_Trans _ nxt dir out) => outToString out ++ dirToString dir ++ stateToString nxt
    end.

Definition tmToString : (option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ)) -> string :=
  fun '(A0, A1, B0, B1) =>
    transToString A0 ++ transToString A1 ++ "_" ++
      transToString B0 ++ transToString B1.

(** Converting decider identifiers to strings
**)
Definition deciderIdentifierToString : DeciderIdentifier -> string :=
  fun decider_id =>
    match decider_id with
    | DECIDER_NIL => "DECIDER_NIL"
    | LOOP1_params_6 => "LOOP1_params_6"
    | NGRAM_CPS_IMPL2_params_1_1_100 => "NGRAM_CPS_IMPL2_params_1_1_100"
    end.

Definition tmAndStatusAndDeciderToString tnf_node decider_id b  :=
tmToString (unmakeTM tnf_node.(TNF_tm)) ++ "," ++ (if (b : bool) then "halt" else "nonhalt") ++ "," ++ (deciderIdentifierToString decider_id).

Redirect "BB2_Extraction/printers" Recursive Extraction tmAndStatusAndDeciderToString.

(**
This is the crucial part of the extraction where we insert the print statements to print 
each enumerated machine and whether it halts or not given the conclusion reached by the Coq proof.

Prints statements are inserted in place of "node_halt" and "node_nonhalt" definitions of the Coq proof, see TNF.v.

In the OCaml code 'Obj.magic' is used to cast between identical types that are both defined in the 'printers' and 'BB2_verified_enumeration' files.
**)

Extract Constant node_halt => "
fun h decider_id a ->
  let _ = print_endline (String.of_seq (List.to_seq (Printers.tmAndStatusAndDeciderToString (Obj.magic h) (Obj.magic decider_id) true)))  in
  a
".

Extract Constant node_nonhalt => "
fun h decider_id a ->
  let _ = print_endline (String.of_seq (List.to_seq (Printers.tmAndStatusAndDeciderToString (Obj.magic h) (Obj.magic decider_id) false)))  in
  a
".

Redirect "BB2_Extraction/BB2_verified_enumeration" Recursive  Extraction q_200_def. 
