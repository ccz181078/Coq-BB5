From CoqBB5 Require Import BB52TheoremPrelim.

Definition q0 := root4_q. 

Definition q_0 := q0.

From CoqBB5 Require Import BB52Theorem_root4_trivial BB52Theorem_root4_nontrivial1.

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
  - admit.
  - apply q_4_trivial_1_HTUB.
  - apply q_4_trivial_2_HTUB.
  - admit.
  - admit.
  - apply q_4_trivial_3_HTUB.
  - apply q_4_trivial_4_HTUB.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
