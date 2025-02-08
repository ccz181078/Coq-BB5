From CoqBB5 Require Import BB52TheoremPrelim.

(** In the OCaml extraction, we do not decompose the TNF tree in several roots (see TNF_Roots/) as this is used only to parallelise the proof. 

The following definitions encompass the entire TNF tree in 200 batches of at most 2^20 machines,
as done before the proof was parallelised, see:

- https://github.com/ccz181078/Coq-BB5/blob/2a4445600061cc21c05f7390a790694972996bad/BB52Theorem.v#L18286
- https://github.com/ccz181078/Coq-BB5/blob/2a4445600061cc21c05f7390a790694972996bad/BB52Theorem.v#L18693
**)
Definition q_0 := root_q_upd1_simplified.
Definition q_suc:SearchQueue->SearchQueue := (fun x => SearchQueue_upds x decider_all 20).
Definition q_200 := Nat.iter 200 q_suc q_0.

Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatBigInt ExtrOcamlString.

(* Opposite to makeTM, transforms TMs to more convenient representation such as "BR0 BL0 CL1 DR1 DR1 EL0 AL1 DR0 DR1 HR1". *)
Definition unmakeTM : TM Σ ->
                      (option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ)) :=
  fun f =>
    (f St0 Σ0, f St0 Σ1, f St1 Σ0, f St1 Σ1, f St2 Σ0, f St2 Σ1, f St3 Σ0, f St3 Σ1, f St4 Σ0, f St4 Σ1).

Extraction SearchQueue_upd.

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
        | St0 => "A" | St1 => "B"| St2 => "C"| St3 => "D"| St4 => "E"
        end.

Definition transToString : option (Trans Σ) -> string :=
  fun o =>
    match o with
    | None => "---"
    | Some (Build_Trans _ nxt dir out) => outToString out ++ dirToString dir ++ stateToString nxt
    end.

Definition tmToString : (option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ)) -> string :=
  fun '(A0, A1, B0, B1, C0, C1, D0, D1, E0, E1) =>
    transToString A0 ++ transToString A1 ++ "_" ++
      transToString B0 ++ transToString B1 ++ "_" ++
      transToString C0 ++ transToString C1 ++ "_" ++
      transToString D0 ++ transToString D1 ++ "_" ++
      transToString E0 ++ transToString E1.

(** Converting decider identifiers to strings
**)
Definition deciderIdentifierToString : DeciderIdentifier -> string :=
  fun decider_id =>
    match decider_id with
    | DECIDER_NIL => "DECIDER_NIL" 
    | LOOP1_params_130 => "LOOP1_params_130"
    | NGRAM_CPS_IMPL2_params_1_1_100 => "NGRAM_CPS_IMPL2_params_1_1_100"
    | NGRAM_CPS_IMPL2_params_2_2_200  => "NGRAM_CPS_IMPL2_params_2_2_200"
    | NGRAM_CPS_IMPL2_params_3_3_400 => "NGRAM_CPS_IMPL2_params_3_3_400"
    | NGRAM_CPS_IMPL1_params_2_2_2_1600 => "NGRAM_CPS_IMPL1_params_2_2_2_1600"
    | NGRAM_CPS_IMPL1_params_2_3_3_1600 => "NGRAM_CPS_IMPL1_params_2_3_3_1600"
    | LOOP1_params_4100 => "LOOP1_params_4100"
    | NGRAM_CPS_IMPL1_params_4_2_2_600 => "NGRAM_CPS_IMPL1_params_4_2_2_600"
    | NGRAM_CPS_IMPL1_params_4_3_3_1600 => "NGRAM_CPS_IMPL1_params_4_3_3_1600"
    | NGRAM_CPS_IMPL1_params_6_2_2_3200 => "NGRAM_CPS_IMPL1_params_6_2_2_3200"
    | NGRAM_CPS_IMPL1_params_6_3_3_3200 => "NGRAM_CPS_IMPL1_params_6_3_3_3200"
    | NGRAM_CPS_IMPL1_params_8_2_2_1600 => "NGRAM_CPS_IMPL1_params_8_2_2_1600"
    | NGRAM_CPS_IMPL1_params_8_3_3_1600 => "NGRAM_CPS_IMPL1_params_8_3_3_1600"
    | TABLE_BASED => "TABLE_BASED"
    | NORMAL_FORM_TABLE_BASED => "NORMAL_FORM_TABLE_BASED"
    end.

Definition tmAndStatusAndDeciderToString tnf_node decider_id b  :=
tmToString (unmakeTM tnf_node.(TNF_tm)) ++ "," ++ (if (b : bool) then "halt" else "nonhalt") ++ "," ++ (deciderIdentifierToString decider_id).

Redirect "BB52Extraction/printers" Recursive Extraction tmAndStatusAndDeciderToString.

(**
This is the crucial part of the extraction where we insert the print statements to print 
each enumerated machine and whether it halts or not given the conclusion reached by the Coq proof.

Prints statements are inserted in place of "node_halt" and "node_nonhalt" definitions of the Coq proof, see TNF.v.

In the OCaml code 'Obj.magic' is used to cast between identical types that are both defined in the 'printers' and 'bb5_verified_enumeration' files.
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

Redirect "BB52Extraction/bb5_verified_enumeration" Recursive Extraction q_200. 
