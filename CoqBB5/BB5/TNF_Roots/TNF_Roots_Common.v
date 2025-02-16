Require Import List.
Require Import ZArith. 

From CoqBB5 Require Import TNF.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Statement. 
From CoqBB5 Require Import BB5_Deciders_Pipeline. 

Definition q_suc:SearchQueue->SearchQueue := (fun x => SearchQueue_upds x decider_all 20).

Lemma q_200_WF_gen :
  forall t : TNF_Node,
    TNF_Node_WF t -> forall n : nat, SearchQueue_WF (N.to_nat BB5_minus_one) (Nat.iter n q_suc (SearchQueue_init t)) t.
Proof.
  intros root root_wf n.
  induction n.
  - apply SearchQueue_init_spec. assumption. 
  - rewrite Nat.iter_succ. 
    apply SearchQueue_upds_spec.
    + exact IHn.
    + apply decider_all_spec.
Qed.

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

Definition TM0: TM Σ :=
  fun x i => None.

Lemma TM0_LE:
  forall tm, LE Σ TM0 tm.
Proof.
  intros.
  unfold LE.
  intros.
  right.
  reflexivity.
Qed.

Lemma UnusedState_TM0 s1:
  UnusedState TM0 s1 <->
  s1 <> St0.
Proof.
split; intro.
- intro H0. subst.
  destruct H as [H [H0 H1]].
  contradiction.
- repeat split; auto 1.
Qed.

Definition root := {| TNF_tm:=TM0; TNF_cnt:=CountHaltTrans (TM0); TNF_ptr:=St1 |}.

Definition TM1 : TM Σ := (makeTM AR0 None None None None None None None None None).
Definition root1 := {| TNF_tm:=TM1; TNF_cnt:=CountHaltTrans (TM1); TNF_ptr:=St1 |}.

Definition TM2 : TM Σ := (makeTM AR1 None None None None None None None None None).
Definition root2 := {| TNF_tm:=TM2; TNF_cnt:=CountHaltTrans (TM2); TNF_ptr:=St1 |}.

Definition TM3 : TM Σ := (makeTM BR0 None None None None None None None None None).
Definition root3 := {| TNF_tm:=TM3; TNF_cnt:=CountHaltTrans (TM3); TNF_ptr:=St2 |}.

Definition TM4 : TM Σ := (makeTM BR1 None None None None None None None None None).
Definition root4 := {| TNF_tm:=TM4; TNF_cnt:=CountHaltTrans (TM4); TNF_ptr:=St2 |}.

Definition root_q := SearchQueue_init root.
Definition root1_q := SearchQueue_init root1.
Definition root2_q := SearchQueue_init root2.
Definition root3_q := SearchQueue_init root3.
Definition root4_q := SearchQueue_init root4.