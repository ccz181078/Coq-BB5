Require Import ZArith.
Require Import Lia.
Require Import List.
Require Export FSets.FMapPositive.

From CoqBB2 Require Import BB2_Statement.
From CoqBB2 Require Import BB2_Deciders_Generic.
From CoqBB2 Require Import List_Tape.
From CoqBB2 Require Import TNF.
From CoqBB2 Require Import Tactics.
From CoqBB2 Require Import TM.
From CoqBB2 Require Import Prelims.
From CoqBB2 Require Import BB2_Encodings.

From CoqBB2 Require Import Deciders_Common.
From CoqBB2 Require Import Decider_Loop.
From CoqBB2 Require Import Decider_NGramCPS.

Set Warnings "-abstract-large-number".

(* Definition decider0 := HaltDecider_nil.
Definition decider1 := halt_decider 130. *)
Definition decider2 := ((loop1_decider 6),LOOP1_params_6).

Definition decider3 := ((NGramCPS_decider_impl2 1 1 100),NGRAM_CPS_IMPL2_params_1_1_100).

Definition decider_all :=
  (HaltDecider_list
(decider2::decider3::nil)).

Lemma decider2_WF: HaltDecider_WF (N.to_nat BB2_minus_one) (fst decider2).
Proof.
  apply loop1_decider_WF.
  unfold BB2_minus_one.
  lia.
Qed.

Lemma decider_all_spec: HaltDeciderWithIdentifier_WF (N.to_nat BB2_minus_one) decider_all.
Proof.
unfold decider_all,HaltDecider_list.
  repeat apply HaltDecider_cons_spec.
  all: try apply NGramCPS_decider_impl2_spec.
  all: try apply NGramCPS_decider_impl1_spec.
  - apply decider2_WF.
  - unfold HaltDecider_nil,HaltDeciderWithIdentifier_WF.
    intro. simpl. trivial.
Qed.