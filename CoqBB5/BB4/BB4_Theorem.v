Require Import ZArith.
Require Import Lia.

From CoqBB4 Require Import Prelims.
From CoqBB4 Require Import BB4_Statement.
From CoqBB4 Require Import BB4_TNF_Enumeration.
From CoqBB4 Require Import BB4_Encodings.
From CoqBB4 Require Import TM.
From CoqBB4 Require Import BB4_Make_TM.
From CoqBB4 Require Import Tactics.
From CoqBB4 Require Import Deciders.Verifier_Halt.

Definition BB4_champion := (makeTM BR1 BL1 AL1 CL0 HR1 DL1 DR1 AR0).

Lemma BB4_lower_bound:
  exists tm,
  HaltsAt _ tm (N.to_nat BB4_minus_one) (InitES Σ Σ0).
Proof.
  exists BB4_champion.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Qed.

Lemma BB4_upperbound:
  forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB4_minus_one.
Proof.
  intros tm n0.
  apply allTM_HTUB.
  trivial.
Qed.

Lemma BB4_value:
  BB4_value_statement.
Proof.
  split.
   - intros tm n0 H.
    invst H.
    epose proof (allTM_HTUB _ _ _ H0) as H1.
    Unshelve. 2: cbn; trivial.
    unfold BB4.
    unfold BB4_minus_one in H1.
    lia.
  - destruct BB4_lower_bound as [tm H].
    exists tm.
    replace (N.to_nat BB4) with (S (N.to_nat BB4_minus_one)).
    1: ctor; apply H.
    unfold BB4_minus_one,BB4. lia.
Qed.

Print Assumptions BB4_value.