Require Import ZArith.
Require Import Lia.
Require Import List.
Require Export FSets.FMapPositive.

From CoqBB3 Require Import BB3_Statement.
From CoqBB3 Require Import BB3_Deciders_Generic.
From CoqBB3 Require Import List_Tape.
From CoqBB3 Require Import TNF.
From CoqBB3 Require Import Tactics.
From CoqBB3 Require Import TM.
From CoqBB3 Require Import Prelims.
From CoqBB3 Require Import BB3_Encodings.

From CoqBB3 Require Import Deciders_Common.
From CoqBB3 Require Import Decider_Loop.
From CoqBB3 Require Import Decider_NGramCPS.

Set Warnings "-abstract-large-number".

(* Definition decider0 := HaltDecider_nil.
Definition decider1 := halt_decider 130. *)
Definition decider2 := ((loop1_decider 21),LOOP1_params_21).

Definition decider3 := ((NGramCPS_decider_impl2 1 1 100),NGRAM_CPS_IMPL2_params_1_1_100).
Definition decider4 := ((NGramCPS_decider_impl2 2 2 200),NGRAM_CPS_IMPL2_params_2_2_200).
Definition decider5 := ((NGramCPS_decider_impl2 3 3 400),NGRAM_CPS_IMPL2_params_3_3_400).
Definition decider6 := ((NGramCPS_decider_impl1 2 2 2 1600),NGRAM_CPS_IMPL1_params_2_2_2_1600).

Definition decider_all :=
  (HaltDecider_list
(decider2::decider3::decider4::decider5::decider6::nil)).

Lemma decider2_WF: HaltDecider_WF (N.to_nat BB3_minus_one) (fst decider2).
Proof.
  apply loop1_decider_WF.
  unfold BB3_minus_one.
  lia.
Qed.

Lemma decider_all_spec: HaltDeciderWithIdentifier_WF (N.to_nat BB3_minus_one) decider_all.
Proof.
unfold decider_all,HaltDecider_list.
  repeat apply HaltDecider_cons_spec.
  all: try apply NGramCPS_decider_impl2_spec.
  all: try apply NGramCPS_decider_impl1_spec.
  - apply decider2_WF.
  - unfold HaltDecider_nil,HaltDeciderWithIdentifier_WF.
    intro. simpl. trivial.
Qed.