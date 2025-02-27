Require Import ZArith.
Require Import Lia.

From CoqBB3 Require Import Prelims.
From CoqBB3 Require Import BB3_Statement.
From CoqBB3 Require Import BB3_TNF_Enumeration.
From CoqBB3 Require Import BB3_Encodings.
From CoqBB3 Require Import TM.
From CoqBB3 Require Import BB3_Make_TM.
From CoqBB3 Require Import Tactics.
From CoqBB3 Require Import Deciders.Verifier_Halt.

Definition BB3_champion := (makeTM BR1 HR1 BL1 CR0 CL1 AL1).

Lemma BB3_lower_bound:
  exists tm,
  HaltsAt _ tm (N.to_nat BB3_minus_one) (InitES Σ Σ0).
Proof.
  exists BB3_champion.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Qed.

Lemma BB3_upperbound:
  forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB3_minus_one.
Proof.
  intros tm n0.
  apply allTM_HTUB.
  trivial.
Qed.

Lemma BB3_value:
  BB3_value_statement.
Proof.
  split.
   - intros tm n0 H.
    invst H.
    epose proof (allTM_HTUB _ _ _ H0) as H1.
    Unshelve. 2: cbn; trivial.
    unfold BB3.
    unfold BB3_minus_one in H1.
    lia.
  - destruct BB3_lower_bound as [tm H].
    exists tm.
    replace (N.to_nat BB3) with (S (N.to_nat BB3_minus_one)).
    1: ctor; apply H.
    unfold BB3_minus_one,BB3. lia.
Qed.

Print Assumptions BB3_value.