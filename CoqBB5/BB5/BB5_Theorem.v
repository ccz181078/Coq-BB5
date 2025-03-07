
Require Import ZArith.
Require Import Lia.

From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Encodings.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import BB5_TNF_Enumeration.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import BB5_Make_TM.
From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import Deciders.Verifier_Halt.

Definition BB5_champion := (makeTM BR1 CL1 CR1 BR1 DR1 EL0 AL1 DL1 HR1 AL0).

Lemma BB5_lower_bound:
  exists tm,
  HaltsAt _ tm (N.to_nat BB5_minus_one) (InitES Σ Σ0).
Proof.
  exists BB5_champion.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Time Qed.

Lemma BB5_upperbound:
  forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB5_minus_one.
Proof.
  intros tm n0.
  apply allTM_HTUB.
  trivial.
Qed.

Lemma BB5_value:
  BB5_value_statement.
Proof.
  unfold BB5_value_statement.
  split.
  - intros tm n0 H.
    invst H.
    epose proof (allTM_HTUB _ _ _ H0) as H1.
    Unshelve. 2: cbn; trivial.
    unfold BB5.
    unfold BB5_minus_one in H1.
    lia.
  - destruct BB5_lower_bound as [tm H].
    exists tm.
    replace (N.to_nat BB5) with (S (N.to_nat BB5_minus_one)).
    1: ctor; apply H.
    unfold BB5_minus_one,BB5. lia.
Qed.

Print Assumptions BB5_value.