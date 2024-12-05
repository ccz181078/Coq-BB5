Require Import List.
Require Import ZArith.
Require Import Logic.FunctionalExtensionality.
Require Import Lia.
Require Import FSets.FMapPositive.

From CoqBB5 Require Import BB52Statement.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import ListTape.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import Encodings.
From CoqBB5 Require Import CustomTactics.
From CoqBB5 Require Import Decider_Pipeline.


From CoqBB5 Require Import Deciders.Decider_Loop.
From CoqBB5 Require Import Deciders.Decider_NGramCPS.


From CoqBB5 Require Import Deciders_CustomParameters.Decider_Loop_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_NGramCPS_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_Verifier_FAR_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_Verifier_FAR_MITM_WDFA_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_RepWL_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_Halt_CustomParameters.



From CoqBB5 Require Import Sporadic_NonHalt.


Definition check_tms(ls:list ((TM Σ)*DeciderType)):=
  map (fun (x:(TM Σ)*DeciderType)=> let (tm,d):=x in getDecider d tm) ls.

(*
Compute (length tm_WA).
Time Definition check_res := Eval vm_compute in (check_tms ((tm_WA))).
Compute (filter (fun x => match x with Result_NonHalt => false | _ => true end) check_res).
Compute check_res.
*)


Definition tm_list :=
  tm_RWL::
  tm_NG0::tm_NG2::tm_NG3::tm_NG4::tm_NG5::tm_NG6::tm_NG7::tm_NG_ge8::
  tm_Ha::
  tm_Lp1::
  tm_NG_LRU::
  tm_NG0'::tm_RWL'::
  tm_DNV::tm_WA::
  (map (fun tm => (tm,Holdout)) tm_holdouts_13)::
  nil.


Definition TM_enc(tm:TM Σ):positive :=
  match TM_to_N tm with
  | N0 => xH
  | Npos v => Pos.succ v
  end.

Fixpoint TM_ins_all(ls:list ((TM Σ)*DeciderType))(mp:PositiveMap.tree DeciderType):PositiveMap.tree DeciderType :=
match ls with
| nil => mp
| (h1,h2)::t => TM_ins_all t (PositiveMap.add (TM_enc h1) h2 mp)
end.

Fixpoint TM_ins_all'(ls:list (list ((TM Σ)*DeciderType)))(mp:PositiveMap.tree DeciderType):PositiveMap.tree DeciderType :=
match ls with
| nil => mp
| h::t => TM_ins_all' t (TM_ins_all h mp)
end.

Time Definition tm_decider_table :=
  Eval vm_compute in (TM_ins_all' tm_list (PositiveMap.empty DeciderType)).

Definition table_based_decider(tm:TM Σ):HaltDecideResult :=
  match PositiveMap.find (TM_enc tm) tm_decider_table with
  | None => Result_Unknown
  | Some d => getDecider d tm
  end.

Lemma table_based_decider_spec: HaltDecider_WF (N.to_nat BB5_minus_one) table_based_decider.
Proof.
  unfold HaltDecider_WF,table_based_decider.
  intros tm.
  destruct (PositiveMap.find (TM_enc tm) tm_decider_table).
  2: trivial.
  apply getDecider_spec.
Qed.

Definition NF_decider(dec:HaltDecider)(tm:TM Σ):HaltDecideResult :=
  match dec (TM_to_NF tm) with
  | Result_NonHalt => Result_NonHalt
  | _ => Result_Unknown
  end.

Lemma NF_decider_spec dec n:
  HaltDecider_WF n dec ->
  HaltDecider_WF n (NF_decider dec).
Proof.
  unfold HaltDecider_WF,NF_decider.
  intro H.
  intro tm.
  specialize (H (TM_to_NF tm)).
  destruct (dec (TM_to_NF tm)).
  1,3: trivial.
  unfold HaltsFromInit.
  unfold HaltsFromInit in H.
  rewrite <-NonHalt_iff.
  rewrite <-NonHalt_iff in H.
  rewrite <-TM_to_NF_spec in H.
  apply H.
Qed.

Definition decider_all :=
  (HaltDecider_list
(decider2::decider3::decider4::decider5::decider6::decider7::decider8::
decider9::decider10::
decider11::decider12::
decider13::decider14::
table_based_decider::
(NF_decider table_based_decider)::
nil)).

Lemma decider_all_spec: HaltDecider_WF (N.to_nat BB5_minus_one) decider_all.
Proof.
  unfold decider_all,HaltDecider_list.
  repeat apply HaltDecider_cons_spec.
  all: try apply NGramCPS_decider_impl2_spec.
  all: try apply NGramCPS_decider_impl1_spec.
  - apply decider2_WF.
  - apply loop1_decider_WF.
    unfold BB5_minus_one. lia.
  - apply table_based_decider_spec.
  - apply NF_decider_spec,table_based_decider_spec.
  - unfold HaltDecider_nil,HaltDecider_WF.
    intro. trivial.
Qed.

Definition q0 := root_q_upd1_simplified.

Definition q_suc:SearchQueue->SearchQueue := (fun x => SearchQueue_upds x decider_all 20).

Definition q_0 := q0.

Definition q_200 := Nat.iter 200 q_suc q_0.

Require Import Extraction.
Require Import ExtrOcamlBasic ExtrOcamlNatBigInt ExtrOcamlString.

Extraction SearchQueue_upd.

Definition unmakeTM : TM Σ ->
                      (option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ)) :=
  fun f =>
    (f St0 Σ0, f St0 Σ1, f St1 Σ0, f St1 Σ1, f St2 Σ0, f St2 Σ1, f St3 Σ0, f St3 Σ1, f St4 Σ0, f St4 Σ1).

Require Import String.
Open Scope string.

Definition printOut : Σ -> string :=
  fun s => match s with
        | Σ0 => "0"
        | Σ1 => "1"
        end.

Definition printDir : Dir -> string :=
  fun s => match s with
           | Dpos => "R"
           | Dneg => "L"
           end.

Definition printState : St -> string :=
  fun s => match s with
        | St0 => "A" | St1 => "B"| St2 => "C"| St3 => "D"| St4 => "E"
        end.

Definition printTrans : option (Trans Σ) -> string :=
  fun o =>
    match o with
    | None => "---"
    | Some (Build_Trans _ nxt dir out) => printOut out ++ printDir dir ++ printState nxt
    end.

Definition printTM : (option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ) * option (Trans Σ)) -> string :=
  fun '(A0, A1, B0, B1, C0, C1, D0, D1, E0, E1) =>
    printTrans A0 ++ printTrans A1 ++ "_" ++
      printTrans B0 ++ printTrans B1 ++ "_" ++
      printTrans C0 ++ printTrans C1 ++ "_" ++
      printTrans D0 ++ printTrans D1 ++ "_" ++
      printTrans E0 ++ printTrans E1 ++ "_".

Definition printTNF_Node n b :=
  printTM (unmakeTM n.(TNF_tm)) ++ ";" ++ (if (b : bool) then "halt" else "nonhalt").

Redirect "printers" Recursive Extraction printTNF_Node.

Extraction insert_node.

Extract Constant insert_node => "fun h r t q2 ->
  let _ = print_endline (String.of_seq (List.to_seq (Printers.printTNF_Node (Obj.magic h) true))) in
  (app r t, q2)
".

Extraction drop_node.

Extract Constant drop_node => "fun h t q2 ->
  let _ = print_endline (String.of_seq (List.to_seq (Printers.printTNF_Node (Obj.magic h) false))) in
  (t, q2)
".

Redirect "code" Recursive Extraction q_200. 
