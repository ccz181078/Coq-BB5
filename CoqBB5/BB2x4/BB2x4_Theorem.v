Require Import ZArith.
Require Import Lia.

From CoqBB2x4 Require Import Prelims.
From CoqBB2x4 Require Import BB2x4_Statement.
From CoqBB2x4 Require Import BB2x4_TNF_Enumeration.
From CoqBB2x4 Require Import BB2x4_Encodings.
From CoqBB2x4 Require Import TM.
From CoqBB2x4 Require Import BB2x4_Make_TM.
From CoqBB2x4 Require Import Tactics.
From CoqBB2x4 Require Import Deciders.Verifier_Halt.

Definition BB2x4_champion := (makeTM BR1 AL2 AR1 AR1 BL1 AL1 BR3 HR1).

Lemma BB2x4_lower_bound:
  exists tm,
  HaltsAt _ tm (N.to_nat BB2x4_minus_one) (InitES Σ Σ0).
Proof.
  exists BB2x4_champion.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Qed.

Lemma BB2x4_upperbound:
  forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB2x4_minus_one.
Proof.
  intros tm n0.
  apply allTM_HTUB.
  trivial.
Qed.

Lemma BB2x4_value:
  BB2x4_value_statement.
Proof.
  split.
   - intros tm n0 H.
    invst H.
    epose proof (allTM_HTUB _ _ _ H0) as H1.
    Unshelve. 2: cbn; trivial.
    unfold BB2x4.
    unfold BB2x4_minus_one in H1.
    lia.
  - destruct BB2x4_lower_bound as [tm H].
    exists tm.
    replace (N.to_nat BB2x4) with (S (N.to_nat BB2x4_minus_one)).
    1: ctor; apply H.
    unfold BB2x4_minus_one,BB2x4. lia.
Qed.

Print Assumptions BB2x4_value.