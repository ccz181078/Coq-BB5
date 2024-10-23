Require Import ZArith.
Require Import Lia.

From BusyCoq Require Import Prelims.
From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import CustomTactics.


Section TM.

Hypothesis Σ:Set.
Hypothesis Σ0:Σ.

Definition HaltsAt(tm:TM Σ)(n:nat)(st:ExecState Σ): Prop :=
  exists st', Steps Σ tm n st st' /\ step Σ tm st' = None.

Definition Halts(tm:TM Σ)(st:ExecState Σ): Prop :=
  exists n, HaltsAt tm n st.

Definition HaltsFromInit(tm:TM Σ): Prop :=
  Halts tm (InitES Σ Σ0).

Lemma Steps_trans {tm n m st st0 st1}:
  Steps Σ tm n st st0 ->
  Steps Σ tm m st0 st1 ->
  Steps Σ tm (m+n) st st1.
Proof.
  intro H.
  gd st1.
  induction m; intros; cbn; invst H0.
  - assumption.
  - ector; eauto.
Qed.

Lemma Steps_unique {tm n st st0 st1}:
  Steps Σ tm n st st0 ->
  Steps Σ tm n st st1 ->
  st0 = st1.
Proof.
  gd st1.
  gd st0.
  induction n; intros st0 st1 H H0; invst H; invst H0.
  - reflexivity.
  - specialize (IHn _ _ H2 H3). subst.
    cg.
Qed.

Lemma Steps_NonHalt {tm m n st st0}:
  m<n ->
  Steps Σ tm n st st0 ->
  ~HaltsAt tm m st.
Proof.
  intros.
  gd st0.
  induction n; intros.
  - lia.
  - assert (H1:m<n\/m=n) by lia.
    destruct H1 as [H1|H1].
    + invst H0.
      apply (IHn H1 _ H3).
    + subst.
      invst H0.
      unfold HaltsAt,Halts.
      intro H1.
      destruct H1 as [st' [H1a H1b]].
      rewrite <-(Steps_unique H2 H1a) in H1b.
      destruct st2. cg.
Qed.

Lemma HaltsAt_unique {tm n1 n2 st}:
  HaltsAt tm n1 st ->
  HaltsAt tm n2 st ->
  n1=n2.
Proof.
  intros.
  pose proof H as H''.
  pose proof H0 as H0''.
  unfold HaltsAt in H,H0.
  pose proof H as H'.
  pose proof H0 as H0'.
  destruct H as [st0 [Ha Hb]].
  destruct H0 as [st1 [H0a H0b]].
  assert (n1=n2\/n1<n2\/n2<n1) by lia.
  destruct H as [H|[H|H]]; cg.
  - destruct (Steps_NonHalt H H0a H'').
  - destruct (Steps_NonHalt H Ha H0'').
Qed.

Definition NonHalt tm st :=
  forall n, exists st', Steps Σ tm n st st'.

Lemma NonHalt_iff {tm st}:
  NonHalt tm st <-> ~Halts tm st.
Proof.
  split; intro.
  - intro H0.
    destruct H0 as [n H0].
    specialize (H (S n)).
    destruct H as [st' H].
    eapply Steps_NonHalt.
    2,3: eassumption.
    lia.
  - intro n.
    induction n.
    + eexists. ector.
    + destruct IHn as [st' IHn].
      unfold Halts,HaltsAt in H.
      destruct (step Σ tm st') as [st''|] eqn:E.
      * exists st''. ector; eassumption.
      * assert False by (apply H; eexists; eexists; split; eassumption).
        contradiction.
Qed.


Definition LE(tm tm':TM Σ): Prop :=
  forall (s:St)(i:Σ),
  tm s i = tm' s i \/
  tm s i = None.

Lemma LE_step tm tm' st st0:
  LE tm tm' ->
  step Σ tm st = Some st0 ->
  step Σ tm' st = Some st0.
Proof.
  unfold LE,step.
  destruct st as [s t].
  intros.
  specialize (H s (t Z0)).
  destruct (tm s (t Z0)) as [[s' d o]|]; cg.
  destruct H; cg.
  rewrite <-H. cg.
Qed.

Lemma LE_Steps {tm tm' n st st0}:
  LE tm tm' ->
  Steps Σ tm n st st0 ->
  Steps Σ tm' n st st0.
Proof.
  intros.
  induction H0.
  - ctor.
  - ector.
    1: apply IHSteps,H.
    eapply LE_step; eassumption.
Qed.

Lemma LE_NonHalts {tm tm' st}:
  LE tm tm' ->
  ~Halts tm st ->
  ~Halts tm' st.
Proof.
  repeat rewrite <-NonHalt_iff.
  unfold NonHalt.
  intros.
  destruct (H0 n) as [st' H1].
  exists st'.
  eapply LE_Steps; eassumption.
Qed.


Hypothesis BB:nat.
Definition HaltTimeUpperBound(st:ExecState Σ)(P:TM Σ->Prop):Prop :=
  forall (tm:TM Σ)(n0:nat), P tm -> HaltsAt tm n0 st -> n0<=BB.


Lemma HaltTimeUpperBound_LE_NonHalt {st tm}:
  ~Halts tm st ->
  HaltTimeUpperBound st (LE tm).
Proof.
  unfold HaltTimeUpperBound.
  intros.
  pose proof (LE_NonHalts H0 H) as H2.
  assert False by (apply H2; eexists; apply H1).
  contradiction.
Qed.

Hypothesis Σ_eqb:Σ->Σ->bool.
Hypothesis Σ_eqb_spec: forall i1 i2, if Σ_eqb i1 i2 then i1=i2 else i1<>i2.

Definition TM_upd tm s i t: TM Σ :=
  fun s0 i0 =>
    if (andb (St_eqb s0 s) (Σ_eqb i0 i)) then t else tm s0 i0.


Lemma LE_HaltsAtES_1 {tm tm0 n st s t}:
  LE tm tm0 ->
  HaltsAt tm n st ->
  Steps Σ tm n st (s,t) ->
  tm0 s (t 0%Z) = None ->
  HaltsAt tm0 n st.
Proof.
  intros.
  unfold HaltsAt.
  epose proof (LE_Steps H H1).
  exists (s,t).
  split. 1: assumption.
  cbn. rewrite H2. reflexivity.
Qed.



Ltac Σ_eq_dec s1 s2 :=
  eq_dec Σ_eqb_spec Σ_eqb s1 s2.


Lemma LE_HaltsAtES_2 {tm tm0 n st s t tr}:
  LE tm tm0 ->
  HaltsAt tm n st ->
  Steps Σ tm n st (s,t) ->
  tm0 s (t 0%Z) = Some tr ->
  LE (TM_upd tm s (t 0%Z) (Some tr)) tm0.
Proof.
  unfold LE.
  intros.
  unfold TM_upd.
  St_eq_dec s0 s.
  - Σ_eq_dec i (t Z0); cbn.
    + left; cg.
    + apply H.
  - apply H.
Qed.


Lemma HaltTimeUpperBound_LE_Halt st tm n s t:
  HaltsAt tm n st ->
  Steps Σ tm n st (s,t) ->
  n<=BB ->
  (forall tr, HaltTimeUpperBound st (LE (TM_upd tm s (t Z0) (Some tr)))) ->
  HaltTimeUpperBound st (LE tm).
Proof.
  intros.
  unfold HaltTimeUpperBound.
  intros.
  destruct (tm0 s (t Z0)) as [tr|] eqn:E.
  - specialize (H2 tr).
    eapply H2.
    2: apply H4.
    eapply LE_HaltsAtES_2; eassumption.
  - pose proof (LE_HaltsAtES_1 H3 H H0 E).
    rewrite (HaltsAt_unique H4 H5).
    assumption.
Qed.



Section swap.

Hypothesis s1 s2:St.
Hypothesis Hneq12: s1<>s2.
Hypothesis Hneq01: s1 <> St0.
Hypothesis Hneq02: s2 <> St0.

Definition St_swap s :=
  if St_eqb s1 s then s2 else
  if St_eqb s2 s then s1 else s.

Definition Trans_swap(tr:Trans Σ) :=
  let (s',d,o):=tr in
  {| nxt:=St_swap s'; dir:=d; out:=o |}.

Definition option_Trans_swap(x:option (Trans Σ)) :=
  match x with
  | Some x0 => Some (Trans_swap x0)
  | None => None
  end.

Definition TM_swap(tm:TM Σ) := 
  fun s i => option_Trans_swap (tm (St_swap s) i).

Definition ExecState_swap(st:ExecState Σ) :=
  let (s,t):=st in
  (St_swap s,t).

Lemma St_swap_swap:
  forall s,
    St_swap (St_swap s) = s.
Proof.
  intros.
  unfold St_swap.
  St_eq_dec s1 s;St_eq_dec s2 s;St_eq_dec s1 s2; auto; try cg.
  - St_eq_dec s2 s2; cg.
  - St_eq_dec s1 s1; cg.
  - St_eq_dec s1 s; try cg.
    St_eq_dec s2 s; try cg.
Qed.

Lemma Trans_swap_swap:
  forall t,
    Trans_swap (Trans_swap t) = t.
Proof.
  intros.
  destruct t.
  unfold Trans_swap.
  f_equal.
  apply St_swap_swap.
Qed.

Lemma option_Trans_swap_swap:
  forall s,
    option_Trans_swap (option_Trans_swap s) = s.
Proof.
  intros.
  destruct s; auto 1.
  unfold option_Trans_swap. f_equal.
  apply Trans_swap_swap.
Qed.

Lemma TM_swap_swap:
  forall tm,
    TM_swap (TM_swap tm) = tm.
Proof.
  intros.
  unfold TM_swap.
  fext. fext.
  rewrite option_Trans_swap_swap,St_swap_swap.
  reflexivity.
Qed.

Lemma ExecState_swap_swap:
  forall st,
    ExecState_swap (ExecState_swap st) = st.
Proof.
  intros.
  destruct st as [s t].
  unfold ExecState_swap.
  f_equal.
  apply St_swap_swap.
Qed.




Lemma step_swap {tm st st0}:
  step Σ (TM_swap tm) st = Some st0 <->
  step Σ tm (ExecState_swap st) = Some (ExecState_swap st0).
Proof.
  destruct st,st0. cbn.
  unfold TM_swap.
  destruct (tm (St_swap s) (σ 0%Z)) eqn:E; cbn.
  2: split; intro; cg.
  destruct t. cbn.
  split; intro; f_equal.
  - invst H.
    f_equal.
    rewrite St_swap_swap; reflexivity.
  - invst H.
    f_equal.
    apply St_swap_swap.
Qed.

Lemma step_halt_swap tm st:
  step Σ (TM_swap tm) st = None <->
  step Σ tm (ExecState_swap st) = None.
Proof.
  destruct st. cbn.
  unfold TM_swap.
  destruct (tm (St_swap s) (σ 0%Z)) eqn:E; cbn.
  2: split; intro; cg.
  destruct t. cbn.
  split; intro; cg.
Qed.


Lemma Steps_swap tm n st st0:
  Steps Σ (TM_swap tm) n st st0 <->
  Steps Σ tm n (ExecState_swap st) (ExecState_swap st0).
Proof.
gd st0.
induction n; intros.
- split; intros; invst H.
  + ctor.
  + ff_inj ExecState_swap_swap H1.
    ctor.
- split; intros.
  + invst H.
    rewrite IHn in H1.
    ector; eauto.
    apply step_swap,H3.
  + invst H.
    pose proof (IHn (ExecState_swap st2)) as IHn'.
    rewrite ExecState_swap_swap in IHn'.
    rewrite <-IHn' in H1.
    ector; eauto.
    apply step_swap.
    rewrite ExecState_swap_swap.
    apply H3.
Qed.


Lemma LE_swap_0 tm tm':
  LE tm tm' -> LE (TM_swap tm) (TM_swap tm').
Proof.
  unfold LE.
  intros.
  unfold TM_swap.
  specialize (H (St_swap s) i).
  destruct H as [H|H]; rewrite H; tauto.
Qed.

Lemma LE_swap tm tm':
  LE tm tm' <-> LE (TM_swap tm) (TM_swap tm').
Proof.
  split.
  - apply LE_swap_0.
  - pose proof (LE_swap_0 (TM_swap tm) (TM_swap tm')) as H.
    repeat rewrite TM_swap_swap in H.
    apply H.
Qed.

Lemma InitES_swap:
  ExecState_swap (InitES Σ Σ0) = InitES Σ Σ0.
Proof.
  unfold InitES. cbn.
  f_equal.
  unfold St_swap.
  St_eq_dec s1 St0; try cg.
  St_eq_dec s2 St0; try cg.
Qed.

Lemma HaltsAt_swap_0 tm n st:
  HaltsAt tm n st ->
  HaltsAt (TM_swap tm) n (ExecState_swap st).
Proof.
  unfold HaltsAt.
  intros.
  destruct H as [st' [H H0]].
  eexists.
  split.
  - rewrite Steps_swap.
    rewrite <-ExecState_swap_swap in H.
    rewrite ExecState_swap_swap.
    apply H.
  - rewrite step_halt_swap,ExecState_swap_swap.
    apply H0.
Qed.

Lemma HaltsAt_swap tm n st:
  HaltsAt tm n st <->
  HaltsAt (TM_swap tm) n (ExecState_swap st).
Proof.
  split.
  - apply HaltsAt_swap_0.
  - pose proof (HaltsAt_swap_0 (TM_swap tm) n (ExecState_swap st)) as H.
    rewrite TM_swap_swap,ExecState_swap_swap in H.
    apply H.
Qed.

Lemma HaltTimeUpperBound_LE_swap tm st:
  HaltTimeUpperBound st (LE tm) -> HaltTimeUpperBound (ExecState_swap st) (LE (TM_swap tm)).
Proof.
  unfold HaltTimeUpperBound.
  intros.
  rewrite LE_swap,TM_swap_swap in H0.
  eapply H.
  1: apply H0.
  rewrite <-ExecState_swap_swap.
  rewrite <-HaltsAt_swap.
  apply H1.
Qed.

Lemma HaltTimeUpperBound_LE_swap_InitES tm:
  HaltTimeUpperBound (InitES Σ Σ0) (LE tm) -> HaltTimeUpperBound (InitES Σ Σ0) (LE (TM_swap tm)).
Proof.
  intro.
  rewrite <-InitES_swap.
  apply HaltTimeUpperBound_LE_swap,H.
Qed.

End swap.



Section rev.
Definition Trans_rev(tr:Trans Σ) :=
  let (s',d,o):=tr in
  {| nxt:=s'; dir:=Dir_rev d; out:=o |}.

Definition option_Trans_rev(o:option (Trans Σ)) :=
  match o with
  | None => None
  | Some tr => Some (Trans_rev tr)
  end.

Definition TM_rev(tm:TM Σ) := 
  fun s i => option_Trans_rev (tm s i).

Definition Tape_rev(t:Z->Σ) :=
  fun x:Z => t (-x)%Z.

Definition ExecState_rev(st:ExecState Σ) :=
  let (s,t):=st in
  (s,Tape_rev t).


Lemma Trans_rev_rev:
  forall t,
    Trans_rev (Trans_rev t) = t.
Proof.
  intros.
  destruct t.
  unfold Trans_rev.
  f_equal.
  destruct dir; auto.
Qed.

Lemma option_Trans_rev_rev:
  forall t,
    option_Trans_rev (option_Trans_rev t) = t.
Proof.
  intros.
  destruct t.
  2: reflexivity.
  cbn.
  f_equal.
  apply Trans_rev_rev.
Qed.

Lemma TM_rev_rev:
  forall tm,
    TM_rev (TM_rev tm) = tm.
Proof.
  intros.
  unfold TM_rev.
  fext. fext.
  apply option_Trans_rev_rev.
Qed.

Lemma Tape_rev_rev:
  forall t,
    Tape_rev (Tape_rev t) = t.
Proof.
  intros.
  unfold Tape_rev.
  fext. f_equal.
  lia.
Qed.

Lemma ExecState_rev_rev:
  forall st,
    ExecState_rev (ExecState_rev st) = st.
Proof.
  intros.
  destruct st as [s t].
  cbn.
  f_equal.
  apply Tape_rev_rev.
Qed.



Lemma step_rev tm st st0:
  step Σ (TM_rev tm) st = Some st0 <->
  step Σ tm (ExecState_rev st) = Some (ExecState_rev st0).
Proof.
  destruct st,st0. cbn.
  unfold Tape_rev. cbn.
  unfold TM_rev.
  destruct (tm s (σ 0%Z)) as [[s' d o]|] eqn:E; cbn.
  2: split; intro; cg.
  split; intro.
  - invst H.
    f_equal; f_equal.
    unfold mov. fext.
    unfold upd.
    destruct d; cbn.
    + assert (x=1\/x<>1)%Z by lia;
      destruct H0;
      destruct ((x + -1 =? 0)%Z) eqn:E0; 
      destruct ((-x + 1 =? 0)%Z) eqn:E1; try lia; cg.
      f_equal; lia.
    + assert (x=-1\/x<>-1)%Z by lia;
      destruct H0;
      destruct ((x + 1 =? 0)%Z) eqn:E0; 
      destruct ((-x + -1 =? 0)%Z) eqn:E1; try lia; cg.
      f_equal; lia.
  - invst H.
    f_equal; f_equal.
    unfold mov.
    unfold mov in H2.
    fext.
    pose proof (fext_inv (-x)%Z H2) as H3.
    cbn in H3.
    assert ((- - x)%Z = x) by lia.
    rewrite H0 in H3.
    rewrite <-H3.
    destruct d; cbn.
    + unfold upd.
      assert (H1:(x=-1\/x<>-1)%Z) by lia.
      destruct H1;
      destruct ((x + 1 =? 0)%Z) eqn:E0;
      destruct ((-x + -1 =? 0)%Z) eqn:E1; try lia; cg.
      f_equal; lia.
    + unfold upd.
      assert (H4:(x=1\/x<>1)%Z) by lia;
      destruct H4;
      destruct ((x + -1 =? 0)%Z) eqn:E0; 
      destruct ((-x + 1 =? 0)%Z) eqn:E1; try lia; cg.
      f_equal; lia.
Qed.


Lemma step_halt_rev tm st:
  step Σ (TM_rev tm) st = None <->
  step Σ tm (ExecState_rev st) = None.
Proof.
  destruct st.
  cbn.
  unfold Tape_rev.
  cbn.
  unfold TM_rev.
  destruct (tm s (σ 0%Z)) eqn:E; cbn.
  2: tauto.
  destruct t; cbn.
  split; intro; cg.
Qed.

Lemma Steps_rev tm n st st0:
  Steps Σ (TM_rev tm) n st st0 <->
  Steps Σ tm n (ExecState_rev st) (ExecState_rev st0).
Proof.
gd st0.
induction n; intros.
- split; intros; invst H.
  + ctor.
  + ff_inj ExecState_rev_rev H1.
    ctor.
- split; intros.
  + invst H.
    rewrite IHn in H1.
    ector; eauto.
    apply step_rev,H3.
  + invst H.
    pose proof (IHn (ExecState_rev st2)) as IHn'.
    rewrite ExecState_rev_rev in IHn'.
    rewrite <-IHn' in H1.
    ector; eauto.
    apply step_rev.
    rewrite ExecState_rev_rev.
    apply H3.
Qed.

Lemma LE_rev_0 tm tm':
  LE tm tm' -> LE (TM_rev tm) (TM_rev tm').
Proof.
  unfold LE.
  intros.
  unfold TM_rev.
  pose proof (H s i) as H0.
  destruct H0 as [H0|H0]; rewrite H0; tauto.
Qed.

Lemma LE_rev tm tm':
  LE tm tm' <-> LE (TM_rev tm) (TM_rev tm').
Proof.
  split.
  - apply LE_rev_0.
  - pose proof (LE_rev_0 (TM_rev tm) (TM_rev tm')) as H.
    repeat rewrite TM_rev_rev in H.
    apply H.
Qed.

Lemma InitES_rev:
  ExecState_rev (InitES Σ Σ0) = InitES Σ Σ0.
Proof.
  reflexivity.
Qed.

Lemma HaltsAt_rev_0 tm n st:
  HaltsAt tm n st ->
  HaltsAt (TM_rev tm) n (ExecState_rev st).
Proof.
  unfold HaltsAt.
  intros.
  destruct H as [st' [H H0]].
  eexists.
  split.
  - rewrite Steps_rev.
    rewrite <-ExecState_rev_rev in H.
    rewrite ExecState_rev_rev.
    apply H.
  - rewrite step_halt_rev,ExecState_rev_rev.
    apply H0.
Qed.

Lemma HaltsAt_rev tm n st:
  HaltsAt tm n st <->
  HaltsAt (TM_rev tm) n (ExecState_rev st).
Proof.
  split.
  - apply HaltsAt_rev_0.
  - pose proof (HaltsAt_rev_0 (TM_rev tm) n (ExecState_rev st)) as H.
    rewrite TM_rev_rev,ExecState_rev_rev in H.
    apply H.
Qed.

Lemma HaltTimeUpperBound_LE_rev tm st:
  HaltTimeUpperBound st (LE tm) -> HaltTimeUpperBound (ExecState_rev st) (LE (TM_rev tm)).
Proof.
  unfold HaltTimeUpperBound.
  intros.
  rewrite LE_rev,TM_rev_rev in H0.
  eapply H.
  1: apply H0.
  rewrite <-ExecState_rev_rev.
  rewrite <-HaltsAt_rev.
  apply H1.
Qed.

Lemma HaltTimeUpperBound_LE_rev_InitES tm:
  HaltTimeUpperBound (InitES Σ Σ0) (LE tm) -> HaltTimeUpperBound (InitES Σ Σ0) (LE (TM_rev tm)).
Proof.
  intro.
  rewrite <-InitES_rev.
  apply HaltTimeUpperBound_LE_rev,H.
Qed.

End rev.

End TM.