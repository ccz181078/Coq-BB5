Require Import Lia.
Require Import List.
Require Import ZArith.

From CoqBB2x4 Require Import TNF.
From CoqBB2x4 Require Import TM.
From CoqBB2x4 Require Import Deciders_Common.
From CoqBB2x4 Require Import Tactics.
From CoqBB2x4 Require Import BB2x4_Encodings.
From CoqBB2x4 Require Import Prelims.
From CoqBB2x4 Require Import BB2x4_Statement.
From CoqBB2x4 Require Import BB2x4_Deciders_Pipeline.

Definition TM0: TM Σ :=
  fun x i => None.

Definition root := {| TNF_tm:=TM0; TNF_cnt:=CountHaltTrans (TM0); TNF_ptr:=St1 |}.
Definition root_q := SearchQueue_init root.

Definition root_q_upd1:=
  (SearchQueue_upd root_q (MakeHaltDeciderWithIdentifier decider2)).

Definition first_trans_is_R(x:TNF_Node):bool :=
  match x.(TNF_tm) St0 Σ0 with
  | Some {| nxt:=_; dir:=Dpos; out:=_ |} => true
  | _ => false
  end.

Definition root_q_upd1_simplified:SearchQueue:=
  (filter first_trans_is_R (fst root_q_upd1), nil).

Definition q_0 := root_q_upd1_simplified.
Definition q_suc:SearchQueue->SearchQueue := (fun x => SearchQueue_upds x decider_all 14).
Definition q_200_def := Nat.iter 200 q_suc q_0.
Definition q_200 : SearchQueue := Eval native_compute in q_200_def.




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
  SearchQueue_WF (N.to_nat BB2x4_minus_one) root_q root.
Proof.
  apply SearchQueue_init_spec,root_WF.
Qed.

Lemma root_q_upd1_WF:
  SearchQueue_WF (N.to_nat BB2x4_minus_one) root_q_upd1 root.
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
  SearchQueue_WF (N.to_nat BB2x4_minus_one) root_q_upd1_simplified root.
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
    destruct H1 as [H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|H1]]]]]]]]]]]]]]]]; try (specialize (H0 x); tauto).
    all:
      clear Ha; clear Hb;
      destruct x as [tm cnt ptr];
      cbn; invst H1;
      rewrite TM_rev_upd'_TM0;
      eapply HaltTimeUpperBound_LE_rev_InitES.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St0; dir := Dpos; out := Σ0 |});
             TNF_cnt := 7;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St0; dir := Dpos; out := Σ1 |});
             TNF_cnt := 7;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St0; dir := Dpos; out := Σ2 |});
             TNF_cnt := 7;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St0; dir := Dpos; out := Σ3 |});
             TNF_cnt := 7;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St1; dir := Dpos; out := Σ0 |});
             TNF_cnt := 7;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St1; dir := Dpos; out := Σ1 |});
             TNF_cnt := 7;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St1; dir := Dpos; out := Σ2 |});
             TNF_cnt := 7;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St1; dir := Dpos; out := Σ3 |});
             TNF_cnt := 7;
             TNF_ptr := St1
           |}); tauto); apply H2.
Qed.

Lemma q_200_spec: q_200 = Nat.iter 200 q_suc q_0.
Proof.
  assert (q_200 = q_200_def) as H  by (native_cast_no_check (eq_refl q_200)).
  rewrite H. unfold q_200_def. reflexivity.
Qed.

Lemma iter_S{A}(f:A->A)(x x0:A) n:
  x0 = Nat.iter n f x ->
  f x0 = Nat.iter (S n) f x.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma q_200_WF:
  SearchQueue_WF (N.to_nat BB2x4_minus_one) q_200 root.
Proof.
  rewrite q_200_spec.
  generalize 200.
  intro n.
  induction n.
  - replace (Nat.iter 0 q_suc q_0) with q_0 by reflexivity.
    unfold q_0,root_q.
    apply root_q_upd1_simplified_WF.
  - replace (Nat.iter (S n) q_suc q_0) with (q_suc (Nat.iter n q_suc q_0)) by (apply iter_S; reflexivity).
    remember (Nat.iter n q_suc q_0) as q.
    clear Heqq.
    unfold q_suc.
    apply SearchQueue_upds_spec.
    + apply IHn.
    + apply decider_all_spec.
Qed.

Lemma q_200_empty:
  q_200 = (nil,nil).
Proof.
  reflexivity.
Qed.

Lemma root_HTUB:
  TNF_Node_HTUB (N.to_nat BB2x4_minus_one) root.
Proof.
  epose proof q_200_WF.
  unfold SearchQueue_WF in H.
  rewrite q_200_empty in H.
  apply H.
  cbn.
  intros.
  contradiction.
Qed.

Lemma TM0_HTUB:
  HaltTimeUpperBound Σ (N.to_nat BB2x4_minus_one) (InitES Σ Σ0) (LE Σ (TM0)).
Proof.
  apply root_HTUB.
Qed.

Lemma allTM_HTUB:
  HaltTimeUpperBound Σ (N.to_nat BB2x4_minus_one) (InitES Σ Σ0) (fun _ => True).
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