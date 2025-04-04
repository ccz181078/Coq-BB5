(**

  In order to parallelize the compilation of the proof, the TNF Enumeration tree is split into several roots each being in its own independent file, see folder `BB5_TNF_Enumeration_Roots/`.

*)

Require Import Lia.
Require Import List.
Require Import ZArith.

From CoqBB5 Require Import TNF.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import Deciders_Common.
From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import BB5_Encodings.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import BB5_Deciders_Pipeline.
From CoqBB5 Require Import TNF_Roots_Common.

From CoqBB5 Require Import TNF_Root_1 TNF_Root_2 TNF_Root_3 TNF_Root_4.

Definition root_q_upd1:=
  (SearchQueue_upd root_q (MakeHaltDeciderWithIdentifier decider2)).

Definition first_trans_is_R(x:TNF_Node):bool :=
  match x.(TNF_tm) St0 Σ0 with
  | Some {| nxt:=_; dir:=Dpos; out:=_ |} => true
  | _ => false
  end.

Definition root_q_upd1_simplified:SearchQueue:=
  (filter first_trans_is_R (fst root_q_upd1), nil).

Lemma root_WF: TNF_Node_WF root.
Proof.
  repeat split.
  1: cbn; cg.
  unfold UnusedState_ptr.
  left.
  intros.
  rewrite UnusedState_TM0.
  destruct s0; unfold St_le; cbn; split; intro; cg; lia.
Qed.

Lemma root_q_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) root_q root.
Proof.
  apply SearchQueue_init_spec,root_WF.
Qed.


Lemma root_q_upd1_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) root_q_upd1 root.
Proof.
  apply SearchQueue_upd_spec.
  - apply root_q_WF.
  - apply decider2_WF.
Qed.

Lemma TM_rev_upd'_TM0 s0 o0:
  (TM_upd' (TM0) St0 Σ0 (Some {| nxt := s0; dir := Dneg; out := o0 |})) =
  (TM_rev Σ (TM_upd' (TM0) St0 Σ0 (Some {| nxt := s0; dir := Dpos; out := o0 |}))).
Proof.
  repeat rewrite TM_upd'_spec.
  fext. fext.
  unfold TM_upd,TM_rev,TM0.
  St_eq_dec x St0.
  - Σ_eq_dec x0 Σ0; cbn; reflexivity.
  - cbn; reflexivity.
Qed.

Lemma root_q_upd1_simplified_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) root_q_upd1_simplified root.
Proof.
  pose proof (root_q_upd1_WF).
  cbn in H.
  destruct H as [Ha Hb].
  cbn.
  split.
  - intros x H0.
    pose proof (Ha x). tauto.
  - intro H0. apply Hb.
    intros x H1.
    destruct H1 as [H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|H1]]]]]]]]; try (specialize (H0 x); tauto).
    1,2,3,4:
      clear Ha; clear Hb;
      destruct x as [tm cnt ptr];
      cbn; invst H1;
      rewrite TM_rev_upd'_TM0;
      eapply HaltTimeUpperBound_LE_rev_InitES.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St0; dir := Dpos; out := Σ0 |});
             TNF_cnt := 9;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St0; dir := Dpos; out := Σ1 |});
             TNF_cnt := 9;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St1; dir := Dpos; out := Σ0 |});
             TNF_cnt := 9;
             TNF_ptr := St2
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St1; dir := Dpos; out := Σ1 |});
             TNF_cnt := 9;
             TNF_ptr := St2
           |}); tauto); apply H2.
Qed.

Lemma root_HTUB:
  TNF_Node_HTUB (N.to_nat BB5_minus_one) root.
Proof.
  eapply SearchQueue_WF_implies_TNF_Node_HTUB.
  2: eapply root_q_upd1_simplified_WF.
  cbn -[BB5_minus_one]. intros x H.
  decompose [or] H; subst; try tauto.
  - apply root1_HTUB.
  - apply root2_HTUB.
  - apply root3_HTUB.
  - apply root4_HTUB.
Qed.

Lemma TM0_HTUB:
  HaltTimeUpperBound Σ (N.to_nat BB5_minus_one) (InitES Σ Σ0) (LE Σ (TM0)).
Proof.
  apply root_HTUB.
Qed.

Lemma allTM_HTUB:
  HaltTimeUpperBound Σ (N.to_nat BB5_minus_one) (InitES Σ Σ0) (fun _ => True).
Proof.
  unfold HaltTimeUpperBound.
  intros.
  eapply TM0_HTUB.
  2: apply H0.
  unfold LE.
  intros.
  right.
  reflexivity.
Qed.