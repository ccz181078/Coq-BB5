(* TNF Root 0RB---_------_------_------_------ *)

Require Import ZArith.
Require Import Lia.

From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import TNF_Roots_Common.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import Encodings.

Definition q_0 := root3_q. 

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

Lemma UnusedState_TM3 s1:
  UnusedState TM3 s1 <->
    s1 <> St0 /\ s1 <> St1.
Proof.
  split; intro.
  - split; intro H0.
    + subst.
      destruct H as [H [H0 H1]].
      contradiction.
    + subst. red in H.
      cbv in H.
      destruct H as [H [H0 H1]].
      specialize (H St0 Σ0).
      cbv in *. congruence.
  - repeat split; auto 1.
    2:{ intros []; cbv.
        all: destruct s1; cbv; try firstorder congruence.
    }
    cbv. intros [] []; try congruence; auto.
    firstorder congruence.
    firstorder congruence.
Qed.

Lemma root3_WF: TNF_Node_WF root3.
Proof.
  repeat split.
  1: cbn; cg.
  unfold UnusedState_ptr.
  left.
  intros.
  rewrite UnusedState_TM3.
  destruct s0; unfold St_le; cbn; split; intro; cg.
  all: try now firstorder congruence.
  all: lia.
Qed.

Lemma q_200_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) q_200 root3.
Proof.
  rewrite q_200_spec.
  apply q_200_WF_gen.
  apply root3_WF.
Qed.

Lemma root3_HTUB:
  TNF_Node_HTUB (N.to_nat BB5_minus_one) root3.
Proof.
  epose proof q_200_WF.
  unfold SearchQueue_WF in H.
  rewrite q_200_empty in H.
  apply H.
  cbn.
  intros.
  contradiction.
Qed.
