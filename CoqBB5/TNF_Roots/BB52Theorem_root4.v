From CoqBB5 Require Import BB52TheoremPrelim.

Definition q0 := root4_q. 

Definition q_0 := q0.

From CoqBB5 Require Import BB52Theorem_root4_trivial BB52Theorem_root4_nontrivial_1 BB52Theorem_root4_nontrivial_2 BB52Theorem_root4_nontrivial_3 BB52Theorem_root4_nontrivial_4 BB52Theorem_root4_nontrivial_5 BB52Theorem_root4_nontrivial_6 BB52Theorem_root4_nontrivial_7 BB52Theorem_root4_nontrivial_8.

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
