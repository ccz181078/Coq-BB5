Require Import List.
Require Import Lia.
Require Import ZArith.

From CoqBB4 Require Import BB4_Statement.
From CoqBB4 Require Import BB4_Make_TM.
From CoqBB4 Require Import List_Routines.
From CoqBB4 Require Import BB4_Deciders_Generic.
From CoqBB4 Require Import Prelims.
From CoqBB4 Require Import Tactics.
From CoqBB4 Require Import TM.
From CoqBB4 Require Import BB4_Encodings.

From CoqBB4 Require Import Deciders_Common.

Section TNF.

Definition CountHaltTrans tm :=
  list_nat_sum (map (fun s=>list_nat_sum (map (fun i => isHaltTrans (tm s i)) Σ_list)) St_list).

Lemma CountHaltTrans_upd {tm s i} tr:
  tm s i = None ->
  S (CountHaltTrans (TM_upd Σ Σ_eqb tm s i (Some tr))) =
  (CountHaltTrans tm).
Proof.
  unfold CountHaltTrans.
  cbn.
  unfold TM_upd.
  intro H.
  destruct s,i; cbn; rewrite H; cbn; lia.
Qed.

Lemma CountHaltTrans_0_NonHalt {tm st}:
  CountHaltTrans tm = 0 ->
  ~Halts Σ tm st.
Proof.
  intro H.
  assert (forall s i, tm s i <> None). {
    intros.
    unfold CountHaltTrans in H.
    cbn in H.
    repeat rewrite Nat.eq_add_0 in H.
    repeat rewrite isHaltTrans_0 in H.
    repeat destruct_and.
    destruct s,i; assumption.
  }
  intro H1.
  unfold Halts,HaltsAt in H1.
  destruct H1 as [n [st' [H1 H2]]].
  destruct st'. cbn in H2.
  destruct (tm s (σ 0%Z)) eqn:E; cg.
  destruct t. cg.
Qed.

Record TNF_Node := {
  TNF_tm: TM Σ;
  TNF_cnt: nat;
  TNF_ptr: St;
}.

Definition TNF_Node_WF(x:TNF_Node):Prop :=
  let (tm,cnt,ptr) := x in
  cnt = CountHaltTrans tm /\
  cnt <> 0 /\
  UnusedState_ptr tm ptr.

Definition St_leb s1 s2 :=
  Nat.leb (St_to_nat s2) (St_to_nat s1).

Lemma St_leb_spec s1 s2:
  if St_leb s1 s2 then St_le s1 s2 else ~(St_le s1 s2).
Proof.
  destruct (St_leb s1 s2) eqn:E.
  - unfold St_le.
    unfold St_leb in E.
    rewrite Nat.leb_le in E.
    apply E.
  - unfold St_le.
    unfold St_leb in E.
    rewrite <-Nat.leb_le.
    cg.
Qed.

Definition TM_upd' tm s i tr :=
  TM_simplify (TM_upd Σ Σ_eqb tm s i tr).

Lemma TM_upd'_spec tm s i tr:
  TM_upd' tm s i tr = TM_upd Σ Σ_eqb tm s i tr.
Proof.
  unfold TM_upd'.
  rewrite TM_simplify_spec.
  reflexivity.
Qed.

Definition TNF_Node_upd(x:TNF_Node) s i tr:=
  let (tm,cnt,ptr):=x in
  {|
    TNF_tm:=TM_upd' tm s i (Some tr);
    TNF_cnt:=Nat.pred cnt;
    TNF_ptr:=(if St_eqb ptr (nxt _ tr) then (St_suc ptr) else ptr)
  |}.

Definition TNF_Node_expand(x:TNF_Node) s i:=
  let (tm,cnt,ptr):=x in
  if Nat.eqb cnt 1 then nil else
    map (TNF_Node_upd x s i)
    (filter (fun tr => St_leb ptr (nxt _ tr)) Trans_list).

Hypothesis BB:nat.


Lemma nat_eqb_spec n1 n2 : if Nat.eqb n1 n2 then n1=n2 else n1<>n2.
Proof.
  destruct (Nat.eqb_spec n1 n2); cg.
Qed.

Ltac nat_eq_dec s1 s2 :=
  eq_dec nat_eqb_spec Nat.eqb s1 s2.

Ltac St_le_dec s1 s2 :=
  eq_dec St_leb_spec St_leb s1 s2.

Definition TNF_Node_HTUB(x:TNF_Node):Prop :=
  let (tm,_,_):=x in
  HaltTimeUpperBound _ BB (InitES Σ Σ0) (LE _ tm).

Lemma TNF_Node_expand_spec {x:TNF_Node}{n s t}:
  HaltsAt Σ (TNF_tm x) n (InitES Σ Σ0) ->
  Steps Σ (TNF_tm x) n (InitES Σ Σ0) (s,t) ->
  n<=BB ->
  TNF_Node_WF x ->
  (forall x', In x' (TNF_Node_expand x s (t Z0)) -> TNF_Node_WF x') /\
  ((forall x', In x' (TNF_Node_expand x s (t Z0)) -> TNF_Node_HTUB x') -> TNF_Node_HTUB x).
Proof.
  destruct x as [tm cnt ptr]. unfold TNF_tm.
  intros.
  split.
  - intros.
    unfold TNF_Node_expand in H3.
    nat_eq_dec cnt 1.
    1: destruct H3.
    epose proof (HaltsAtES_Trans H H0) as H5.
    destruct H2 as [H2a [H2b H2c]].
    rewrite in_map_iff in H3.
    destruct H3 as [tr [H3a H3b]].
    cbn in H3a. rewrite TM_upd'_spec in H3a.
    rewrite <-H3a.
    repeat split.
    + destruct cnt; cg. unfold Nat.pred.
      epose proof (CountHaltTrans_upd tr H5) as H6.
      rewrite <-H2a in H6.
      injection H6.
      intro H7. rewrite H7. reflexivity.
    + destruct cnt; cg. unfold Nat.pred. cg.
    + eapply UnusedState_ptr_upd; eauto 1.
      rewrite filter_In in H3b.
      destruct H3b as [_ H3b].
      St_le_dec ptr (nxt _ tr); cg.
  - unfold TNF_Node_HTUB.
    intros.
    destruct H2 as [H2a [H2b H2c]].
    eapply HaltTimeUpperBound_LE_HaltAtES_UnusedState_ptr; eauto 1.
    intros.
    unfold TNF_Node_expand in H3.
    nat_eq_dec cnt 1.
    + apply HaltTimeUpperBound_LE_NonHalt.
      apply CountHaltTrans_0_NonHalt.
      epose proof (HaltsAtES_Trans H H0) as H5.
      epose proof (CountHaltTrans_upd tr H5) as H6. cg.
    + specialize (H3 (TNF_Node_upd {| TNF_tm := tm; TNF_cnt := cnt; TNF_ptr := ptr |} s (t 0%Z) tr)).
      rewrite <-TM_upd'_spec.
      apply H3. clear H3.
      rewrite in_map_iff. exists tr.
      split. 1: reflexivity.
      rewrite filter_In.
      split.
      1: apply Trans_list_spec.
      St_le_dec ptr (nxt _ tr); cg.
Qed.

Lemma TNF_Node_NonHalt {x:TNF_Node}:
  ~ HaltsFromInit Σ Σ0 (TNF_tm x) ->
  TNF_Node_HTUB x.
Proof.
  destruct x as [tm cnt ptr].
  intros. cbn.
  apply HaltTimeUpperBound_LE_NonHalt,H.
Qed.

Definition SearchQueue :=
  ((list TNF_Node)*(list TNF_Node))%type.

Definition SearchQueue_WF (q:SearchQueue) x0:=
  let (q1,q2):=q in
  (forall x, In x (q1++q2) -> TNF_Node_WF x) /\
  ((forall x, In x (q1++q2) -> TNF_Node_HTUB x) -> TNF_Node_HTUB x0).

(**
The following two definitions are needed for printing purpose: the OCaml extraction will insert print statements
in place of these definitions. See BB52Extraction.v.
**)
Definition node_halt (h : TNF_Node) (decider_id: DeciderIdentifier) {A} : A -> A := fun a => a.
Definition node_nonhalt (h : TNF_Node) (decider_id: DeciderIdentifier) {A} : A -> A := fun a => a.

Definition SearchQueue_upd(q:SearchQueue)(f:HaltDeciderWithIdentifier) :=
  match q with
  | (h::t,q2) =>
    let res := f (TNF_tm h) in
    let decider_id := snd res in
    match fst res with
    | Result_Halt s i => node_halt h decider_id (TNF_Node_expand h s i ++ t, q2)
    | Result_NonHalt => node_nonhalt h decider_id (t, q2)
    | Result_Unknown => (t,h::q2)
    end
  | _ => q
  end.

Lemma SearchQueue_upd_spec {q x0 f}:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_upd q f) x0.
Proof.
  destruct q as [q1 q2].
  destruct q1 as [|h q1].
  1: tauto.
  cbn.
  intros Hq Hf.
  destruct Hq as [Hq1 Hq2].
  specialize (Hf (TNF_tm h)).
  destruct (fst (f (TNF_tm h))).
  - cbn.
    split.
    + intros.
      repeat rewrite in_app_iff in H.
      rewrite or_assoc in H.
      rewrite <-in_app_iff in H.
      destruct H.
      2: apply Hq1; tauto.
      destruct Hf as [n [t [Hf1 [Hf2 [Hf3 Hf4]]]]].
      subst.
      eapply TNF_Node_expand_spec; eauto 1.
      apply Hq1. tauto.
    + intros. apply Hq2. intros.
      destruct H0.
      * subst.
        destruct Hf as [n [t [Hf1 [Hf2 [Hf3 Hf4]]]]].
        eapply TNF_Node_expand_spec; eauto 1.
        1: apply Hq1; tauto.
        intros.
        apply H.
        subst.
        repeat rewrite in_app_iff.
        tauto.
      * apply H.
        repeat rewrite in_app_iff.
        rewrite in_app_iff in H0.
        tauto.
  - split.
    + intros; apply Hq1; tauto.
    + intros; apply Hq2. intros.
      destruct H0. 2: auto 2.
      subst.
      apply TNF_Node_NonHalt,Hf.
  - split.
    + intros. apply Hq1.
      rewrite in_app_iff.
      rewrite in_app_iff in H. cbn in H.
      tauto.
    + intros. apply Hq2. intros. apply H.
      rewrite in_app_iff.
      rewrite in_app_iff in H0. cbn.
      tauto.
Qed.

Definition SearchQueue_upd_bfs(q:SearchQueue)(f:HaltDeciderWithIdentifier) :=
  match q with
  | (h::t,q2) =>
    match fst (f (TNF_tm h)) with
    | Result_Halt s i => (t,(TNF_Node_expand h s i)++q2)
    | Result_NonHalt => (t,q2)
    | Result_Unknown => (t,h::q2)
    end
  | _ => q
  end.

Lemma SearchQueue_upd_bfs_spec {q x0 f}:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_upd_bfs q f) x0.
Proof.
  intros.
  pose proof (SearchQueue_upd_spec H H0).
  unfold SearchQueue_WF.
  unfold SearchQueue_upd_bfs.
  unfold SearchQueue_WF in H1.
  unfold SearchQueue_upd in H1.
  destruct q as [q1 q2].
  destruct q1 as [|h t].
  1: apply H1.
  destruct (fst (f (TNF_tm h))); auto 1.
  assert (
    forall x, In x ((TNF_Node_expand h s i ++ t) ++ q2) <-> In x (t ++ TNF_Node_expand h s i ++ q2)
  ). {
  intros.
  repeat rewrite in_app_iff.
  tauto.
  }
  split.
  - intro. rewrite <-H2.
    apply H1.
  - intro. apply H1.
    intros.
    apply H3; auto 1.
    rewrite <-H2.
    apply H4.
Qed.

Definition SearchQueue_reset(q:SearchQueue):SearchQueue :=
  match q with
  | (q1,q2) => (q1++q2,nil)
  end.

Lemma SearchQueue_reset_spec {q x0}:
  SearchQueue_WF q x0 ->
  SearchQueue_WF (SearchQueue_reset q) x0.
Proof.
  unfold SearchQueue_WF,SearchQueue_reset.
  destruct q as [q1 q2].
  intro.
  split.
  - intros. apply H.
    rewrite app_nil_r in H0. apply H0.
  - intros. apply H.
    intros. apply H0. rewrite app_nil_r. apply H1.
Qed.

Definition SearchQueue_init(x0:TNF_Node):SearchQueue := (x0::nil,nil).

Definition SearchQueue_init_spec(x0:TNF_Node):
  TNF_Node_WF x0 ->
  SearchQueue_WF (SearchQueue_init x0) x0.
Proof.
  intro.
  unfold SearchQueue_WF,SearchQueue_init.
  cbn.
  split.
  - intros. destruct H0 as [H0|[]]; cg.
  - intros. apply H0. tauto.
Qed.

Fixpoint SearchQueue_upds q f (n:nat) :=
match (fst q) with
| nil => q
| _ =>
  match n with
  | O => SearchQueue_upd q f
  | S n0 => SearchQueue_upds (SearchQueue_upds q f n0) f n0
  end
end.

Lemma SearchQueue_upds_spec q x0 f n:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_upds q f n) x0.
Proof.
  intros.
  gd q.
  induction n; cbn; intros.
  - destruct (fst q); auto 1.
    eapply SearchQueue_upd_spec; eauto 1.
  - destruct (fst q); auto 1.
    apply IHn,IHn,H.
Qed.

Fixpoint SearchQueue_upds_bfs q f (n:nat) :=
  match n with
  | O => q
  | S n0 => SearchQueue_upd_bfs (SearchQueue_upds_bfs q f n0) f
  end.

Lemma SearchQueue_upds_bfs_spec q x0 f n:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_upds_bfs q f n) x0.
Proof.
  intros.
  gd q.
  induction n; cbn; intros; auto 1.
  apply SearchQueue_upd_bfs_spec; auto 1.
  apply IHn,H.
Qed.

Definition SearchQueue_bfs q f :=
  SearchQueue_reset (SearchQueue_upds_bfs q f (length (fst q))).

Lemma SearchQueue_bfs_spec q x0 f:
  SearchQueue_WF q x0 ->
  HaltDeciderWithIdentifier_WF BB f ->
  SearchQueue_WF (SearchQueue_bfs q f) x0.
Proof.
  intros.
  unfold SearchQueue_bfs.
  apply SearchQueue_reset_spec.
  apply SearchQueue_upds_bfs_spec; auto 1.
Qed.

End TNF.