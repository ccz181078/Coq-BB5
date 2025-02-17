(* TNF Root 1RB---_------_------_------_------ *)

Require Import ZArith.
Require Import Lia.

From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import BB5_Deciders_Pipeline.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import TNF_Roots_Common.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import BB5_Encodings.

Definition q0 := root4_q. 

Definition q_0 := q0.

From CoqBB5 Require Import TNF_Roots.TNF_Root_4.TNF_Root_4_1 TNF_Roots.TNF_Root_4.TNF_Root_4_2 TNF_Roots.TNF_Root_4.TNF_Root_4_3_leaf TNF_Roots.TNF_Root_4.TNF_Root_4_4_leaf TNF_Roots.TNF_Root_4.TNF_Root_4_5 TNF_Roots.TNF_Root_4.TNF_Root_4_6 TNF_Roots.TNF_Root_4.TNF_Root_4_7_leaf TNF_Roots.TNF_Root_4.TNF_Root_4_8_leaf TNF_Roots.TNF_Root_4.TNF_Root_4_9 TNF_Roots.TNF_Root_4.TNF_Root_4_10 TNF_Roots.TNF_Root_4.TNF_Root_4_11 TNF_Roots.TNF_Root_4.TNF_Root_4_12.

Lemma UnusedState_TM4 s1:
  UnusedState TM4 s1 <->
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

Lemma root4_WF: TNF_Node_WF root4.
Proof.
  repeat split.
  1: cbn; cg.
  unfold UnusedState_ptr.
  left.
  intros.
  rewrite UnusedState_TM4.
  destruct s0; unfold St_le; cbn; split; intro; cg.
  all: try now firstorder congruence.
  all: lia.
Qed.

Lemma root4_q_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) root4_q root4.
Proof.
  apply SearchQueue_init_spec,root4_WF.
Qed.

Lemma root4_HTUB:
  TNF_Node_HTUB (N.to_nat BB5_minus_one) root4.
Proof.
  eapply SearchQueue_WF_implies_TNF_Node_HTUB.
  2:{ eapply SearchQueue_upds_spec.
      eapply root4_q_WF.
      eapply decider_all_spec.
  }
  instantiate (1 := 0).
  cbn -[BB5_minus_one].
  intros ? H.
  decompose [or] H; subst; try tauto.
  - apply root4_nontrivial_1_HTUB.
  - apply root4_nontrivial_2_HTUB.
  - apply q_4_trivial_1_HTUB.
  - apply q_4_trivial_2_HTUB.
  - apply root4_nontrivial_3_HTUB.
  - apply root4_nontrivial_4_HTUB.
  - apply q_4_trivial_3_HTUB.
  - apply q_4_trivial_4_HTUB.
  - apply root4_nontrivial_5_HTUB.
  - apply root4_nontrivial_6_HTUB.
  - apply root4_nontrivial_7_HTUB.
  - apply root4_nontrivial_8_HTUB.
Qed.
