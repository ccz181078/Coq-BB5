Require Import ZArith.
Require Import Lia.

From CoqBB2 Require Import Prelims.
From CoqBB2 Require Import BB2_Statement.
From CoqBB2 Require Import BB2_TNF_Enumeration.
From CoqBB2 Require Import BB2_Encodings.
From CoqBB2 Require Import TM.
From CoqBB2 Require Import BB2_Make_TM.
From CoqBB2 Require Import Tactics.
From CoqBB2 Require Import Deciders.Verifier_Halt.

Definition BB2_champion := (makeTM BR1 BL1 AL1 HR1).

Lemma BB2_lower_bound:
  exists tm,
  HaltsAt _ tm (N.to_nat BB2_minus_one) (InitES Σ Σ0).
Proof.
  exists BB2_champion.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Qed.

Lemma BB2_upperbound:
  forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB2_minus_one.
Proof.
  intros tm n0.
  apply allTM_HTUB.
  trivial.
Qed.

Lemma BB2_value:
  BB2_value_statement.
Proof.
  split.
   - intros tm n0 H.
    invst H.
    epose proof (allTM_HTUB _ _ _ H0) as H1.
    Unshelve. 2: cbn; trivial.
    unfold BB2.
    unfold BB2_minus_one in H1.
    lia.
  - destruct BB2_lower_bound as [tm H].
    exists tm.
    replace (N.to_nat BB2) with (S (N.to_nat BB2_minus_one)).
    1: ctor; apply H.
    unfold BB2_minus_one,BB2. lia.
Qed.

Print Assumptions BB2_value.