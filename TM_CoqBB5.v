Require Import ZArith.
Require Import Lia.

From BusyCoq Require Import Prelims.
From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import CustomTactics.
From BusyCoq Require Import Encodings.





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

Definition UnusedState(tm:TM Σ)(s:St): Prop :=
  (forall s0 i,
    match tm s0 i with
    | None => True
    | Some tr => nxt Σ tr <> s
    end) /\
  (forall i, tm s i = None) /\
  s <> St0.

Definition isUnusedState tm s: bool :=
  forallb_St (fun s0 =>
  forallb_Σ (fun i =>
  match tm s0 i with
  | None => true
  | Some tr => negb (St_eqb (nxt Σ tr) s)
  end)) &&&
  forallb_Σ (fun i => match tm s i with None => true | _ => false end) &&&
  negb (St_eqb s St0).

Lemma isUnusedState_spec tm s:
  if isUnusedState tm s then UnusedState tm s else ~UnusedState tm s.
Proof.
  unfold isUnusedState.
  repeat rewrite andb_shortcut_spec.
  destruct forallb_St eqn:E.
  - destruct forallb_Σ eqn:E0.
    + St_eq_dec s St0.
      * cbn.
        intro H0.
        destruct H0 as [Ha [Hb Hc]].
        cg.
      * cbn.
        repeat split; auto 1.
        -- intros.
           rewrite forallb_St_spec in E.
           specialize (E s0).
           rewrite forallb_Σ_spec in E.
           specialize (E i).
           destruct (tm s0 i). 2: trivial.
           St_eq_dec (nxt _ t) s; cbn in E; cg.
        -- intros.
           rewrite forallb_Σ_spec in E0.
           specialize (E0 i).
           destruct (tm s i); cg.
    + cbn.
      intro H.
      destruct H as [Ha [Hb Hc]].
      assert (forallb_Σ (fun i : Σ => match tm s i with
                             | Some _ => false
                             | None => true
                             end) = true). {
        rewrite forallb_Σ_spec.
        intro i.
        rewrite Hb.
        reflexivity.
      } cg.
  - cbn.
    intros H.
    destruct H as [Ha [Hb Hc]].
    assert (forallb_St
      (fun s0 : St =>
       forallb_Σ
         (fun i : Σ =>
          match tm s0 i with
          | Some tr => negb (St_eqb (nxt Σ tr) s)
          | None => true
          end)) = true). {
      rewrite forallb_St_spec.
      intro s0.
      rewrite forallb_Σ_spec.
      intro i.
      specialize (Ha s0 i).
      destruct (tm s0 i); cg.
      St_eq_dec (nxt _ t) s; cbn; cg.
    } cg.
Qed.

Definition UnusedState_ptr tm s1:=
  (forall s0, UnusedState tm s0 <-> St_le s0 s1) \/
  ((forall s0, ~UnusedState tm s0) /\ forall s0, St_le s1 s0).

Lemma step_UnusedState {tm s0 t0 s t}:
  step Σ tm (s0, t0) = Some (s, t) ->
  ~ UnusedState tm s.
Proof.
  intros. intro.
  cbn in H.
  destruct H0 as [H0a [H0b H0c]].
  specialize (H0a s0 (t0 Z0)).
  destruct (tm s0 (t0 Z0)) as [[s' d o]|] eqn:E; cg.
  invst H. cbn in H0a. cg.
Qed.


Lemma Steps_UnusedState {tm n s t}:
  Steps Σ tm n (InitES Σ Σ0) (s,t) ->
  ~ UnusedState tm s.
Proof.
  intro H.
  gd s. gd t.
  destruct n; intros.
  - invst H.
    intro H0.
    destruct H0 as [H0a [H0b H0c]].
    cg.
  - invst H.
    destruct st0 as [s0 t0].
    eapply step_UnusedState,H3.
Qed.

Ltac Σ_eq_dec s1 s2 :=
  eq_dec Σ_eqb_spec Σ_eqb s1 s2.

Lemma Trans_swap_id s1 s2 t:
  nxt Σ t <> s1 ->
  nxt Σ t <> s2 ->
  t = Trans_swap Σ s1 s2 t.
Proof.
  intros.
  destruct t.
  unfold Trans_swap.
  f_equal.
  cbn in H,H0.
  unfold St_swap.
  St_eq_dec s1 nxt; subst; try cg.
  St_eq_dec s2 nxt; subst; try cg.
Qed.


Lemma HaltTimeUpperBound_LE_HaltsAtES_UnusedState{tm n s t bb}:
  HaltsAt _ tm n (InitES Σ Σ0) ->
  Steps _ tm n (InitES Σ Σ0) (s,t) ->
  forall s1 s2 d o,
    UnusedState tm s1 ->
    UnusedState tm s2 ->
    HaltTimeUpperBound _ bb (InitES Σ Σ0) (LE Σ (TM_upd Σ Σ_eqb tm s (t Z0) (Some {| nxt:=s1; dir:=d; out:=o |}))) ->
    HaltTimeUpperBound _ bb (InitES Σ Σ0) (LE Σ (TM_upd Σ Σ_eqb tm s (t Z0) (Some {| nxt:=s2; dir:=d; out:=o |}))).
Proof.
  intros.
  St_eq_dec s1 s2; rename H4 into n0.
  1: subst; auto 1.
  pose proof (Steps_UnusedState H0) as H'0.
  assert (U1:s1<>s) by (intro X; subst; contradiction).
  assert (U2:s2<>s) by (intro X; subst; contradiction).
  destruct H1 as [H1a [H1b H1c]].
  destruct H2 as [H2a [H2b H2c]].
  assert (H':TM_swap Σ s1 s2
        (TM_upd Σ Σ_eqb tm s (t 0%Z) (Some {| nxt := s1; dir := d; out := o |})) =
        (TM_upd Σ Σ_eqb tm s (t 0%Z) (Some {| nxt := s2; dir := d; out := o |}))). {
    fext. fext.
    unfold TM_upd,TM_swap,option_Trans_swap. cbn.
    unfold St_swap. cbn.
    St_eq_dec s1 x.
    {
      subst.
      St_eq_dec s2 s; cg. cbn.
      rewrite H1b,H2b.
      St_eq_dec x s; cg. cbn. cg.
    }
    St_eq_dec s2 x.
    {
      subst.
      St_eq_dec s1 s; cg. cbn.
      rewrite H1b,H2b.
      St_eq_dec x s; cg. cbn. cg.
    }
    St_eq_dec x s.
    {
      subst. cbn.
      (Σ_eq_dec x0 (t Z0)).
      - subst. f_equal.
        cbn. f_equal. unfold St_swap.
        St_eq_dec s1 s1; cg.
      - specialize (H1a s x0).
        specialize (H2a s x0).
        destruct (tm s x0) as [[s' d1 o1]|]; cg. f_equal.
        cbn in H1a,H2a.
        erewrite <-Trans_swap_id; eauto 1.
    }
    cbn.
    specialize (H1a x x0).
    specialize (H2a x x0).
    destruct (tm x x0) as [[s' d1 o1]|]; cg. f_equal.
    cbn in H1a,H2a.
    erewrite <-Trans_swap_id; eauto 1.
  }
  rewrite <-H'.
  apply HaltTimeUpperBound_LE_swap_InitES; assumption.
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

Lemma UnusedState_dec tm s:
  (UnusedState tm s)\/(~UnusedState tm s).
Proof.
  pose proof (isUnusedState_spec tm s).
  destruct (isUnusedState tm s); tauto.
Qed.

Lemma HaltTimeUpperBound_LE_HaltAtES_MergeUnusedState tm n s t (P:St->Prop) BB:
  HaltsAt _ tm n (InitES Σ Σ0) ->
  Steps _ tm n (InitES Σ Σ0) (s,t) ->
  n<=BB ->
  ((exists s0, P s0 /\ UnusedState tm s0) \/
   (forall s0, ~UnusedState tm s0)) ->
  (forall s0, ~UnusedState tm s0 -> P s0) ->
  (forall tr,
    P (nxt _ tr) ->
    HaltTimeUpperBound _ BB (InitES Σ Σ0) (LE _ (TM_upd Σ Σ_eqb tm s (t Z0) (Some tr)))) ->
  HaltTimeUpperBound _ BB (InitES Σ Σ0) (LE _ tm).
Proof.
  intros.
  destruct H2 as [H2|H2].
  - eapply HaltTimeUpperBound_LE_Halt; eauto 1.
    1: apply Σ_eqb_spec.
    intro.
    destruct (UnusedState_dec tm (nxt _ tr)) as [H5|H5].
    + destruct H2 as [s0 [H2a H2b]].
      destruct tr as [s1 d1 o1].
      cbn in H5.
      eapply HaltTimeUpperBound_LE_HaltsAtES_UnusedState.
      * apply H.
      * apply H0.
      * apply H2b.
      * apply H5.
      * apply H4,H2a.
    + apply H4,H3,H5.
  - eapply HaltTimeUpperBound_LE_Halt; eauto 1.
    1: apply Σ_eqb_spec.
    intro. apply H4,H3,H2.
Qed.



Lemma HaltTimeUpperBound_LE_HaltAtES_UnusedState_ptr {tm n s t s1 BB}:
  HaltsAt _ tm n (InitES Σ Σ0) ->
  Steps _ tm n (InitES Σ Σ0) (s,t) ->
  n<=BB ->
  UnusedState_ptr tm s1 ->
  (forall tr,
    St_le s1 (nxt _ tr) ->
    HaltTimeUpperBound _ BB (InitES Σ Σ0) (LE _ (TM_upd Σ Σ_eqb tm s (t Z0) (Some tr)))) ->
  HaltTimeUpperBound _ BB (InitES Σ Σ0) (LE _ tm).
Proof.
  intros.
  destruct H2 as [H2|H2].
  - eapply HaltTimeUpperBound_LE_HaltAtES_MergeUnusedState with (P:=St_le s1); eauto 1.
    + left.
      exists s1.
      rewrite H2.
      split; unfold St_le; lia.
    + intros. rewrite H2 in H4.
      unfold St_le. unfold St_le in H4. lia.
  - destruct H2 as [H2a H2b].
    eapply HaltTimeUpperBound_LE_HaltAtES_MergeUnusedState with (P:=St_le s1); eauto 1.
    tauto.
Qed.

Lemma HaltsAtES_Trans {tm n st s t}:
  HaltsAt Σ tm n st ->
  Steps Σ tm n st (s, t) ->
  tm s (t Z0) = None.
Proof.
  intros.
  destruct H as [[s0 t0] [Ha Hb]].
  pose proof (Steps_unique _ Ha H0) as H.
  invst H.
  unfold step in Hb.
  destruct (tm s (t Z0)); cg.
  destruct t0; cg.
Qed.

Lemma UnusedState_upd {tm n s t tr s1}:
  HaltsAt _ tm n (InitES Σ Σ0) ->
  Steps _ tm n (InitES Σ Σ0) (s,t) ->
  UnusedState (TM_upd Σ Σ_eqb tm s (t Z0) (Some tr)) s1 <->
  (UnusedState tm s1 /\ s1<>nxt _ tr).
Proof.
intros.
split.
- unfold UnusedState. intro.
  destruct H1 as [H1a [H1b H1c]].
  repeat split; auto 1.
  + intros.
    specialize (H1a s0 i).
    unfold TM_upd in H1a.
    St_eq_dec s0 s.
    * Σ_eq_dec i (t Z0); cbn in H1a.
      -- subst.
         rewrite (HaltsAtES_Trans H H0). trivial.
      -- apply H1a.
    * apply H1a.
  + intros.
    specialize (H1b i).
    unfold TM_upd in H1b.
    St_eq_dec s1 s.
    * Σ_eq_dec i (t Z0); cbn in H1b.
      -- subst. cg.
      -- apply H1b.
    * apply H1b.
  + intro H2. subst.
    specialize (H1a s (t Z0)).
    unfold TM_upd in H1a.
    St_eq_dec s s; cg.
    Σ_eq_dec (t Z0) (t Z0); cg.
- intro H1.
  destruct H1 as [H1 H1d].
  pose proof H1 as U1.
  unfold UnusedState.
  destruct H1 as [H1a [H1b H1c]].
  repeat split; auto 1.
  + intros.
    specialize (H1a s0 i).
    unfold TM_upd.
    St_eq_dec s0 s.
    * Σ_eq_dec i (t Z0); cbn; cg.
    * apply H1a.
  + intros.
    specialize (H1b i).
    assert (E:s1<>s) by (intro; subst; apply (Steps_UnusedState H0),U1).
    unfold TM_upd.
    St_eq_dec s1 s; cg.
    apply H1b.
Qed.

Lemma UnusedState_ptr_upd {tm n s t s1 tr}:
  HaltsAt _ tm n (InitES Σ Σ0) ->
  Steps _ tm n (InitES Σ Σ0) (s,t) ->
  UnusedState_ptr tm s1 ->
  St_le s1 (nxt _ tr) ->
  UnusedState_ptr (TM_upd Σ Σ_eqb tm s (t Z0) (Some tr)) (if St_eqb s1 (nxt _ tr) then (St_suc s1) else s1).
Proof.
intros.
St_eq_dec s1 (nxt _ tr).
- unfold UnusedState_ptr.
  unfold UnusedState_ptr in H1.
  destruct H1 as [H1|[H1a H1b]].
  + subst. clear H2.
    St_eq_dec (nxt _ tr) (St_suc (nxt _ tr)).
    * pose proof (St_suc_eq _ H2).
      rewrite <-H2.
      right.
      split. 2: apply H3.
      intros.
      erewrite UnusedState_upd; eauto 1.
      rewrite H1.
      intro H'.
      destruct H' as [H'0 H'1].
      apply H'1.
      apply St_to_nat_inj.
      specialize (H3 s0).
      unfold St_le in H3,H'0.
      lia.
    * left. intros.
      erewrite UnusedState_upd; eauto 1.
      rewrite H1.
      pose proof (St_suc_neq _ H2).
      unfold St_le.
      assert (E0:s0 = nxt _ tr <-> St_to_nat s0 = St_to_nat (nxt _ tr)). {
        split; intro.
        - cg.
        - apply St_to_nat_inj,H4.
      }
      rewrite E0.
      lia.
  + right. split.
    * intro.
      erewrite UnusedState_upd; eauto 1.
      intro H'.
      eapply H1a.
      destruct H' as [H' _]. apply H'.
    * intro. subst.
      specialize (H1b s0).
      pose proof (St_suc_le (nxt _ tr)) as H1.
      unfold St_le.
      unfold St_le in H1,H1b.
      lia.
- unfold UnusedState_ptr.
  unfold UnusedState_ptr in H1.
  destruct H1 as [H1|[H1a H1b]].
  + assert (E:~St_le (nxt _ tr) s1). {
      unfold St_le. unfold St_le in H2.
      assert (St_to_nat (s1) <> St_to_nat (nxt _ tr)) by (intro X; apply H3,St_to_nat_inj,X).
      lia.
    }
    left.
    intro. rewrite <-H1.
    erewrite UnusedState_upd; eauto 1.
    rewrite <-H1 in E.
    split; intro H4.
    * apply H4.
    * split. 1: apply H4.
      intro X. subst. apply E,H4.
  + right. split; auto 1.
    intro.
    erewrite UnusedState_upd; eauto 1.
    intro H'. eapply H1a. apply H'.
Qed.

Definition AL0 := Some {| nxt:=St0; dir:=Dneg; out:=Σ0 |}.
Definition AL1 := Some {| nxt:=St0; dir:=Dneg; out:=Σ1 |}.
Definition AR0 := Some {| nxt:=St0; dir:=Dpos; out:=Σ0 |}.
Definition AR1 := Some {| nxt:=St0; dir:=Dpos; out:=Σ1 |}.

Definition BL0 := Some {| nxt:=St1; dir:=Dneg; out:=Σ0 |}.
Definition BL1 := Some {| nxt:=St1; dir:=Dneg; out:=Σ1 |}.
Definition BR0 := Some {| nxt:=St1; dir:=Dpos; out:=Σ0 |}.
Definition BR1 := Some {| nxt:=St1; dir:=Dpos; out:=Σ1 |}.

Definition CL0 := Some {| nxt:=St2; dir:=Dneg; out:=Σ0 |}.
Definition CL1 := Some {| nxt:=St2; dir:=Dneg; out:=Σ1 |}.
Definition CR0 := Some {| nxt:=St2; dir:=Dpos; out:=Σ0 |}.
Definition CR1 := Some {| nxt:=St2; dir:=Dpos; out:=Σ1 |}.

Definition DL0 := Some {| nxt:=St3; dir:=Dneg; out:=Σ0 |}.
Definition DL1 := Some {| nxt:=St3; dir:=Dneg; out:=Σ1 |}.
Definition DR0 := Some {| nxt:=St3; dir:=Dpos; out:=Σ0 |}.
Definition DR1 := Some {| nxt:=St3; dir:=Dpos; out:=Σ1 |}.

Definition EL0 := Some {| nxt:=St4; dir:=Dneg; out:=Σ0 |}.
Definition EL1 := Some {| nxt:=St4; dir:=Dneg; out:=Σ1 |}.
Definition ER0 := Some {| nxt:=St4; dir:=Dpos; out:=Σ0 |}.
Definition ER1 := Some {| nxt:=St4; dir:=Dpos; out:=Σ1 |}.

Definition HL0:option (Trans Σ) := None.
Definition HL1:option (Trans Σ) := None.
Definition HR0:option (Trans Σ) := None.
Definition HR1:option (Trans Σ) := None.

Definition makeTM:
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(TM Σ) :=
fun A0 A1 B0 B1 C0 C1 D0 D1 E0 E1 s i =>
match s,i with
| St0,Σ0 => A0
| St0,Σ1 => A1
| St1,Σ0 => B0
| St1,Σ1 => B1
| St2,Σ0 => C0
| St2,Σ1 => C1
| St3,Σ0 => D0
| St3,Σ1 => D1
| St4,Σ0 => E0
| St4,Σ1 => E1
end.
