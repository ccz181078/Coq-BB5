From CoqBB5 Require Import BB52TheoremPrelim.
From CoqBB5 Require Import BB52Theorem_root3 BB52Theorem_root4.

Lemma SearchQueue_WF_implies_TNF_Node_HTUB BB (q : SearchQueue) root :
  (  let (q1, q2) := q in
     (forall x : TNF_Node, In x (q1 ++ q2) -> TNF_Node_HTUB BB x)) ->
  SearchQueue_WF BB q root ->
  TNF_Node_HTUB BB root.
Proof.
  intros. red in H0.
  destruct q as [q1 q2].
  eapply H0.
  eauto.
Qed.

Lemma root_HTUB:
  TNF_Node_HTUB (N.to_nat BB5_minus_one) root.
Proof.
  eapply SearchQueue_WF_implies_TNF_Node_HTUB.
  2: eapply root_q_upd1_simplified_WF.
  cbn -[BB5_minus_one]. intros x H.
  decompose [or] H; subst; try tauto.
  - admit.
  - admit.
  - refine root3_HTUB.
  - refine root4_HTUB.
Admitted.

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
