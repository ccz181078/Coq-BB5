Require Import List.

From CoqBB5 Require Import CustomTactics.
From CoqBB5 Require Import BB52Statement.
From CoqBB5 Require Import Translation.
From CoqBB5 Require Import TM_CoqBB5.
From CoqBB5 Require Import ListTape.

Require Import
  BusyCoq.(Finned1 Finned2 Finned3 Finned4 Finned5
  Skelet1 Skelet10 Skelet15 Skelet17 Skelet26 Skelet33 Skelet34 Skelet35).

Definition Finned1 := makeTM BR1 EL0 CR1 BR1 DR1 CL1 EL0 BR0 HR1 AL1.
Definition Finned2 := makeTM BR1 AR1 CR1 BL1 DL0 AR0 AR1 EL1 HR1 DL0.
Definition Finned3 := makeTM BR1 ER1 CL1 BR1 AR0 DL0 BL1 DL1 HR1 AR0.
Definition Finned4 := makeTM BR1 AL1 CL0 ER0 HR1 DL1 AR1 CL0 AR1 ER1.
Definition Finned5 := makeTM BR1 AL1 CL0 ER0 HR1 DL1 AL1 CL0 AR1 ER1.
Definition Skelet1 := makeTM BR1 DR1 CL1 CR0 AR1 DL1 ER0 BL0 HR1 CR1.
Definition Skelet10 := makeTM BR1 AR0 CL0 AR1 ER1 DL1 CL1 DL0 HR1 BR0.
Definition Skelet15 := makeTM BR1 HR1 CR1 BL1 DL1 ER1 BL1 DL0 AR1 CR0.
Definition Skelet17 := makeTM BR1 HR1 CL0 ER1 DL0 CL1 AR1 BL1 BR0 AR0.
Definition Skelet26 := makeTM BR1 DL1 CR1 BR0 AL1 CR1 EL1 AL0 CL1 HR1.
Definition Skelet33 := makeTM BR1 CL1 CR0 BR0 DL1 AL0 EL1 HR1 AL1 ER1.
Definition Skelet34 := makeTM BR1 CL1 CR0 BR0 DL1 AL0 EL1 HR1 AL1 AR1.
Definition Skelet35 := makeTM BR1 CL1 CR0 BR0 DL1 AL0 EL1 HR1 AL1 AL0.

Definition tm_holdouts_13 :=
  Finned1::Finned2::Finned3::Finned4::Finned5::
  Skelet1::Skelet10::Skelet15::Skelet17::Skelet26::Skelet33::Skelet34::Skelet35::
  nil.

Lemma Finned1_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned1.
Proof.
  translate_nonhalt Finned1.tm Finned1.nonhalt.
Qed.

Lemma Finned2_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned2.
Proof.
  translate_nonhalt Finned2.tm Finned2.nonhalt.
Qed.

Lemma Finned3_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned3.
Proof.
  assert (H:~HaltsFromInit Σ Σ0 (to_TM Finned3.tm)) by (apply to_NonHalt,Finned3.nonhalt).
  unfold HaltsFromInit in H.
  unfold HaltsFromInit.
  rewrite <-NonHalt_iff in H.
  rewrite <-NonHalt_iff.
  rewrite TM_to_rev_NF_spec in H.
  replace (TM_to_rev_NF (to_TM Finned3.tm)) with Finned3 in H.
  1: apply H.
  fext. fext.
  destruct x,x0; reflexivity.
Qed.

Lemma Finned4_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned4.
Proof.
  translate_nonhalt Finned4.tm Finned4.nonhalt.
Qed.

Lemma Finned5_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned5.
Proof.
  translate_nonhalt Finned5.tm Finned5.nonhalt.
Qed.

Lemma Skelet10_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet10.
Proof.
  translate_nonhalt Skelet10.tm Skelet10.nonhalt.
Qed.

Lemma Skelet15_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet15.
Proof.
  translate_nonhalt Skelet15.tm Skelet15.nonhalt.
Qed.

Lemma Skelet26_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet26.
Proof.
  translate_nonhalt Skelet26.tm Skelet26.nonhalt.
Qed.

Lemma Skelet33_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet33.
Proof.
  translate_nonhalt Skelet33.tm Skelet33.nonhalt.
Qed.

Lemma Skelet34_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet34.
Proof.
  translate_nonhalt Skelet34.tm Skelet34.nonhalt.
Qed.

Lemma Skelet35_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet35.
Proof.
  translate_nonhalt Skelet35.tm Skelet35.nonhalt.
Qed.

Lemma Skelet1_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet1.
Proof.
  translate_nonhalt Skelet1.tm Skelet1.nonhalt.
Qed.

Lemma Skelet17_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet17.
Proof.
  translate_nonhalt Skelet17.tm Skelet17.nonhalt.
Qed.