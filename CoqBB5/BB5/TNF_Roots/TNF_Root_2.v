(* TNF Root 1RA---_------_------_------_------ *)

Require Import ZArith.
Require Import Lia.

From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import TNF_Roots_Common.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import Encodings.

Definition q0 := root2_q. 

Definition q_0 := q0.

Definition q_1_def := q_suc q_0.
Definition q_1 := Eval native_compute in q_1_def.

Lemma iter_S{A}(f:A->A)(x x0:A) n:
  x0 = Nat.iter n f x ->
  f x0 = Nat.iter (S n) f x.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Ltac q_rw q_x q_x_def :=
  assert (H:q_x = q_x_def) by (native_cast_no_check (eq_refl q_x));
  rewrite H; unfold q_x_def; clear H; apply iter_S.

Lemma q_200_spec: q_1 = Nat.iter 1 q_suc q_0.
Proof.
  reflexivity. 
Qed.

Lemma q_200_empty:
  q_1 = (nil,nil).
Proof.
  reflexivity.
Qed.

Lemma UnusedState_TM2 s1:
  UnusedState TM2 s1 <->
    s1 <> St0.
Proof.
  split; intro.
  - intro H0. subst.
    destruct H as [H [H0 H1]].
    contradiction.
  - repeat split; auto 1.
    2:{ intros []; cbv.
        all: destruct s1; cbv; try congruence.
    }
    cbv. intros [] []; try congruence; auto.
Qed.

Lemma root2_WF: TNF_Node_WF root2.
Proof.
  repeat split.
  1: cbn; cg.
  unfold UnusedState_ptr.
  left.
  intros.
  rewrite UnusedState_TM2.
  destruct s0; unfold St_le; cbn; split; intro; cg; lia.
Qed.

Lemma q_200_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) q_1 root2.
Proof.
  rewrite q_200_spec.
  apply q_200_WF_gen.
  apply root2_WF.
Qed.

Lemma root2_HTUB:
  TNF_Node_HTUB (N.to_nat BB5_minus_one) root2.
Proof.
  epose proof q_200_WF.
  unfold SearchQueue_WF in H.
  rewrite q_200_empty in H.
  apply H.
  cbn.
  intros.
  contradiction.
Qed.
