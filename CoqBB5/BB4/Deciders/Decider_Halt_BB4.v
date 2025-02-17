Require Import Lia.
Require Import ZArith.

From CoqBB4 Require Import TM.
From CoqBB4 Require Import BB4_Statement.
From CoqBB4 Require Import BB4_Encodings.
From CoqBB4 Require Import Deciders_Common.
From CoqBB4 Require Import Decider_Halt.

Set Warnings "-abstract-large-number".

Definition halt_decider_max := halt_decider 106.
Lemma halt_decider_max_spec: HaltDecider_WF (N.to_nat BB4_minus_one) halt_decider_max.
Proof.
  eapply halt_decider_WF.
  unfold BB4_minus_one. lia.
Qed.