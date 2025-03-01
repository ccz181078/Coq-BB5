Require Import ZArith.
Require Import Lia.

From CoqBB2x3 Require Import Prelims.
From CoqBB2x3 Require Import BB2x3_Statement.
From CoqBB2x3 Require Import BB2x3_TNF_Enumeration.
From CoqBB2x3 Require Import BB2x3_Encodings.
From CoqBB2x3 Require Import TM.
From CoqBB2x3 Require Import BB2x3_Make_TM.
From CoqBB2x3 Require Import Tactics.
From CoqBB2x3 Require Import Deciders.Verifier_Halt.

(* 1RZ_2LA2RB1LB *)

Definition BB2x3_champion := (makeTM BR1 BL2 HR1 AL2 BR2 BL1).

Lemma BB2x3_lower_bound:
  exists tm,
  HaltsAt _ tm (N.to_nat BB2x3_minus_one) (InitES Σ Σ0).
Proof.
  exists BB2x3_champion.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Qed.

Lemma BB2x3_upperbound:
  forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB2x3_minus_one.
Proof.
  intros tm n0.
  apply allTM_HTUB.
  trivial.
Qed.

Lemma BB2x3_value:
  BB2x3_value_statement.
Proof.
  split.
   - intros tm n0 H.
    invst H.
    epose proof (allTM_HTUB _ _ _ H0) as H1.
    Unshelve. 2: cbn; trivial.
    unfold BB2x3.
    unfold BB2x3_minus_one in H1.
    lia.
  - destruct BB2x3_lower_bound as [tm H].
    exists tm.
    replace (N.to_nat BB2x3) with (S (N.to_nat BB2x3_minus_one)).
    1: ctor; apply H.
    unfold BB2x3_minus_one,BB2x3. lia.
Qed.

Print Assumptions BB2x3_value.