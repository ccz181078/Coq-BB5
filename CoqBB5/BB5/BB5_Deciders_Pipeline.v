Require Import ZArith.
Require Import Lia.
Require Import List.
Require Export FSets.FMapPositive.

From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import BB5_Deciders_Generic.
From CoqBB5 Require Import BB5_Deciders_Hardcoded.
From CoqBB5 Require Import List_Tape.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import BB5_Make_TM.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Encodings.

From CoqBB5 Require Import Deciders_Common.
From CoqBB5 Require Import Decider_Halt.
From CoqBB5 Require Import Decider_Loop.
From CoqBB5 Require Import Decider_NGramCPS.
From CoqBB5 Require Import Decider_RepWL.
From CoqBB5 Require Import Verifier_FAR.
From CoqBB5 Require Import Verifier_WFAR.
From CoqBB5 Require Import BB5_Sporadic_Machines.


From CoqBB5 Require Export BB5_Deciders_Hardcoded_Parameters.Decider_Loop_Hardcoded_Parameters.
From CoqBB5 Require Export BB5_Deciders_Hardcoded_Parameters.Decider_NGramCPS_Hardcoded_Parameters.
From CoqBB5 Require Export BB5_Deciders_Hardcoded_Parameters.Verifier_FAR_Hardcoded_Certificates.
From CoqBB5 Require Export BB5_Deciders_Hardcoded_Parameters.Verifier_WFAR_Hardcoded_Certificates.
From CoqBB5 Require Export BB5_Deciders_Hardcoded_Parameters.Decider_RepWL_Hardcoded_Parameters.
From CoqBB5 Require Export BB5_Deciders_Hardcoded_Parameters.Decider_Halt_Hardcoded_Parameters.

Set Warnings "-abstract-large-number".

(* Definition decider0 := HaltDecider_nil.
Definition decider1 := halt_decider 130. *)
Definition decider2 := ((loop1_decider 130), LOOP1_params_130).

Definition decider3 := ((NGramCPS_decider_impl2 1 1 100), NGRAM_CPS_IMPL2_params_1_1_100).
Definition decider4 := ((NGramCPS_decider_impl2 2 2 200),NGRAM_CPS_IMPL2_params_2_2_200).
Definition decider5 := ((NGramCPS_decider_impl2 3 3 400),NGRAM_CPS_IMPL2_params_3_3_400).
Definition decider6 := ((NGramCPS_decider_impl1 2 2 2 1600),NGRAM_CPS_IMPL1_params_2_2_2_1600).
Definition decider7 := ((NGramCPS_decider_impl1 2 3 3 1600),NGRAM_CPS_IMPL1_params_2_3_3_1600).

Definition decider8 := ((loop1_decider 4100),LOOP1_params_4100).

Definition decider9 := ((NGramCPS_decider_impl1 4 2 2 600),NGRAM_CPS_IMPL1_params_4_2_2_600).
Definition decider10 := ((NGramCPS_decider_impl1 4 3 3 1600),NGRAM_CPS_IMPL1_params_4_3_3_1600).
Definition decider11 := ((NGramCPS_decider_impl1 6 2 2 3200),NGRAM_CPS_IMPL1_params_6_2_2_3200).
Definition decider12 := ((NGramCPS_decider_impl1 6 3 3 3200),NGRAM_CPS_IMPL1_params_6_3_3_3200).
Definition decider13 := ((NGramCPS_decider_impl1 8 2 2 1600),NGRAM_CPS_IMPL1_params_8_2_2_1600).
Definition decider14 := ((NGramCPS_decider_impl1 8 3 3 1600),NGRAM_CPS_IMPL1_params_8_3_3_1600).

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

Definition tm_decider_table :=
  Eval vm_compute in (TM_ins_all' tm_list (PositiveMap.empty DeciderType)).

Definition table_based_decider(tm:TM Σ):HaltDecideResult :=
  match PositiveMap.find (TM_enc tm) tm_decider_table with
  | None => Result_Unknown
  | Some d => getDecider d tm
  end.

Definition NF_decider(dec:HaltDecider)(tm:TM Σ):HaltDecideResult :=
  match dec (TM_to_NF tm) with
  | Result_NonHalt => Result_NonHalt
  | _ => Result_Unknown
  end.

Definition decider_all :=
  (HaltDecider_list
(decider2::decider3::decider4::decider5::decider6::decider7::decider8::
decider9::decider10::
decider11::decider12::
decider13::decider14::
(table_based_decider,TABLE_BASED)::
((NF_decider table_based_decider),NORMAL_FORM_TABLE_BASED)::
nil)).


Lemma table_based_decider_spec: HaltDecider_WF (N.to_nat BB5_minus_one) table_based_decider.
Proof.
  unfold HaltDecider_WF,table_based_decider.
  intros tm.
  destruct (PositiveMap.find (TM_enc tm) tm_decider_table).
  2: trivial.
  apply getDecider_spec.
Qed.

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

Lemma decider2_WF: HaltDecider_WF (N.to_nat BB5_minus_one) (fst decider2).
Proof.
  apply loop1_decider_WF.
  unfold BB5_minus_one.
  lia.
Qed.

Lemma decider_all_spec: HaltDeciderWithIdentifier_WF (N.to_nat BB5_minus_one) decider_all.
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
  - unfold HaltDecider_nil,HaltDeciderWithIdentifier_WF.
    intro. simpl. trivial.
Qed.