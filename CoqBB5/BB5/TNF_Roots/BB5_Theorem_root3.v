(* TNF Root 0RB---_------_------_------_------ *)

From CoqBB5 Require Import BB5_Theorem_Prelim.

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
