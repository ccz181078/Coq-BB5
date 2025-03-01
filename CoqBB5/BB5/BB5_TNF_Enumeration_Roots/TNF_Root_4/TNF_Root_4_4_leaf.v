(* TNF Root 1RB---_1RA---_------_------_------ *)

Require Import ZArith.
Require Import List.
Require Import Lia.

From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Encodings.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import TNF_Roots_Common.

From CoqBB5 Require Import BB5_Deciders_Pipeline.

Definition q_1_manual := (SearchQueue_upds root4_q decider_all 0).

Definition q_4_trivial_2 := nth 3 (fst q_1_manual) root.
Definition q_4_trivial_2' : SearchQueue := q_suc (SearchQueue_init q_4_trivial_2).

Lemma q_4_trivial_2'_nil :
  q_4_trivial_2' = (nil, nil).
Proof.
  reflexivity.
Qed.

Lemma q_4_trivial_2'_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) q_4_trivial_2' q_4_trivial_2.
Proof.
  unfold q_4_trivial_2'.
  change ((q_suc (SearchQueue_init q_4_trivial_2))) with
    (Nat.iter 1 q_suc (SearchQueue_init q_4_trivial_2)).
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

Lemma q_4_trivial_2_HTUB:
  TNF_Node_HTUB (N.to_nat BB5_minus_one) q_4_trivial_2.
Proof.
  epose proof q_4_trivial_2'_WF.
  unfold SearchQueue_WF in H.
  rewrite q_4_trivial_2'_nil in H.
  apply H.
  cbn.
  intros.
  contradiction.
Qed.