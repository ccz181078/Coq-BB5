(* TNF Root 1RB---_0RA---_------_------_------ *)

Require Import ZArith.
Require Import List.
Require Import Lia.

From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Encodings.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import TNF_Roots_Common.

From CoqBB5 Require Import BB5_Deciders_Pipeline.

Definition q_1_manual := (SearchQueue_upds root4_q decider_all 0).

Definition root4_nontrivial_1 := nth 0 (fst q_1_manual) root.

Definition q_0 := SearchQueue_init root4_nontrivial_1.

Definition q_200_def := Nat.iter 200 q_suc q_0.
Definition q_200 : SearchQueue := Eval native_compute in q_200_def.

Lemma q_200_spec: q_200 = Nat.iter 200 q_suc q_0.
Proof.
  assert (q_200 = q_200_def) as H  by (native_cast_no_check (eq_refl q_200)).
  rewrite H. unfold q_200_def. reflexivity.
Qed.

Lemma q_200_empty:
  q_200 = (nil,nil).
Proof.
  reflexivity.
Qed.

Lemma q_200_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) q_200 root4_nontrivial_1.
Proof.
  rewrite q_200_spec.
  apply q_200_WF_gen.
  red. repeat split.
  1: cbn; cg.
  unfold UnusedState_ptr.
  left.
  intros.
  unfold UnusedState. cbn. unfold St_le. cbn.
  destruct s0; cbn; split; try lia.
  all: repeat split; try congruence.
  all: try intros ? [].
  all: try (intros []; try congruence).
  all: try destruct s0; cbn; try tauto.
  all: try congruence.
  destruct H0. specialize (H0 Σ0). cbn in *. 
  congruence.
Qed.

Lemma root4_nontrivial_1_HTUB:
  TNF_Node_HTUB (N.to_nat BB5_minus_one) root4_nontrivial_1.
Proof.
  epose proof q_200_WF.
  unfold SearchQueue_WF in H.
  rewrite q_200_empty in H.
  apply H.
  cbn.
  intros.
  contradiction.
Qed.
