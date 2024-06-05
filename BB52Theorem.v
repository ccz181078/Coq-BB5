Require Import List.
Require Import ZArith.
Require Import Logic.FunctionalExtensionality.
Require Import Lia.
Require Import FSets.FMapPositive.
From BusyCoq Require Import BB52Statement.

Set Warnings "-abstract-large-number".

Ltac invst H := inversion H; subst.
Ltac ctor := constructor.
Ltac ector := econstructor.
Ltac fext := apply functional_extensionality; intro.
Ltac gd x := generalize dependent x.
Ltac cg := try congruence.


Ltac clr_eqrefl:=
  repeat match goal with
  | H: ?A = ?A |- _ => clear H
  end.

Ltac clr_dup:=
  repeat match goal with
  | H:?A, H':?A |- _ => clear H'
  end.

Ltac clrs:=
  clr_eqrefl; clr_dup.



Definition is_inj{T1 T2}(f:T1->T2):=
  forall a b, f a = f b -> a = b.



Lemma ffx_eq_x_inj{A}:
  forall f:A->A,
  (forall x:A, f (f x) = x) ->
  forall x y:A, f x = f y -> x = y.
Proof.
  intros.
  assert ((f (f x)) = (f (f y))) as H1. {
    rewrite H0,H. reflexivity.
  }
  rewrite H,H in H1.
  apply H1.
Qed.

Ltac ff_inj RR H := pose proof (ffx_eq_x_inj _ RR _ _ H); subst.


Fixpoint positive_len(x:positive):nat :=
match x with
| xH => O
| xI x0 => S (positive_len x0)
| xO x0 => S (positive_len x0)
end.


Fixpoint enc_v1(x:positive):positive :=
match x with
| xH => xH
| xI x0 => xI (xI (enc_v1 x0))
| xO x0 => xI (xO (enc_v1 x0))
end.

Lemma enc_v1_eq a1 b1 a2 b2:
  append (enc_v1 a1) (xO b1) = append (enc_v1 a2) (xO b2) ->
  (a1 = a2 /\ b1 = b2).
Proof.
  gd a2.
  induction a1; destruct a2; cbn; intros; cg; invst H.
  1,2: destruct (IHa1 a2 H1).
  all: split; cg.
Qed.

Definition enc_pair(x:positive*positive):positive :=
  let (x1,x2):=x in
  append (enc_v1 (Pos.of_succ_nat (positive_len x1))) (xO (append x1 x2)).

Lemma enc_pair_inj: is_inj enc_pair.
Proof.
  intros x1 x2 H.
  destruct x1 as [a1 b1].
  destruct x2 as [a2 b2].
  unfold enc_pair in H.
  destruct (enc_v1_eq _ _ _ _ H) as [Ha Hb]. clear H.
  assert (positive_len a1 = positive_len a2) by lia. clear Ha.
  gd a2.
  induction a1; destruct a2; cbn; intros; cg;
  invst Hb;
  invst H;
  assert ((a1,b1)=(a2,b2)) by auto 2;
  cg.
Qed.

Fixpoint enc_list(x:list positive):positive :=
match x with
| nil => xH
| h::t => enc_pair (h,enc_list t)
end.

Lemma enc_list_inj: is_inj enc_list.
Proof.
  intros x1 x2 H.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; intros; cg.
  - cbn in H. destruct ((Pos.of_succ_nat (positive_len h2))); cbn in H; cg.
  - cbn in H. destruct ((Pos.of_succ_nat (positive_len h1))); cbn in H; cg.
  - epose proof (enc_pair_inj _ _ H).
    invst H0.
    f_equal.
    apply IHt1; assumption.
Qed.





Notation "x &&& y" := (if x then y else false) (at level 80, right associativity).
Notation "x ||| y" := (if x then true else y) (at level 85, right associativity).

Lemma andb_shortcut_spec(a b:bool):
  (a&&&b) = (a&&b)%bool.
Proof.
  reflexivity.
Qed.

Lemma orb_shortcut_spec(a b:bool):
  (a|||b) = (a||b)%bool.
Proof.
  reflexivity.
Qed.






Definition set_ins{T}(enc:T->positive)(s:list T * PositiveMap.tree unit)(x:T):(list T * PositiveMap.tree unit)*bool :=
  let enc := (enc x) in
  match PositiveMap.find enc (snd s) with
  | None => ((x::fst s, PositiveMap.add enc tt (snd s)),false)
  | Some _ => (s,true)
  end.

Definition set_in{T}(enc:T->positive)(s:list T * PositiveMap.tree unit)(x:T):Prop :=
  PositiveMap.find (enc x) (snd s) = Some tt.

Definition set_WF{T}(enc:T->positive)(s:list T * PositiveMap.tree unit):Prop :=
  forall (x:T),
    set_in enc s x <->
    In x (fst s).


Lemma set_ins_spec{T} enc (enc_inj: is_inj enc) s (x:T) s' flag:
  set_WF enc s ->
  set_ins enc s x = (s',flag) ->
  (set_WF enc s' /\
  (flag=true -> (s'=s /\ set_in enc s x))).
Proof.
  unfold set_WF,set_ins,set_in.
  intros.
  destruct (PositiveMap.find (enc x) (snd s)) as [v|] eqn:E.
  - invst H0.
    split.
    1: assumption.
    intros.
    destruct v.
    split; cg.
  - invst H0. clear H0.
    split; intros. 2: cg.
    cbn.
    rewrite (PositiveMapAdditionalFacts.gsspec).
    destruct (PositiveMap.E.eq_dec (enc x0) (enc x)) as [e|e].
    + pose proof (enc_inj _ _ e); subst.
      split; tauto.
    + assert (x<>x0) by cg.
      split; intro.
      * right. rewrite <-H. apply H1.
      * rewrite <-H in H1.
        destruct H1 as [H1|H1]; cg.
Qed.



Lemma empty_set_WF{T}(enc:T->positive):
  set_WF enc (nil, PositiveMap.empty unit).
Proof.
  unfold set_WF.
  intros. cbn.
  split; intro.
  2: contradiction.
  unfold set_in in H.
  rewrite PositiveMap.gempty in H. cg.
Qed.












Fixpoint pop_back{T}(x:T)(ls:list T):(list T) :=
  match ls with
  | h::t =>
    x::(pop_back h t)
  | nil => nil
  end.

Lemma pop_back_len{T} (h:T) t:
  length (pop_back h t) = length t.
Proof.
  gd h.
  induction t; intros; cbn.
  - reflexivity.
  - f_equal; apply IHt.
Qed.

Lemma pop_back__nth_error{T} (h:T) t:
  forall n:nat,
  n<length t ->
  nth_error (pop_back h t) n =
  nth_error (h::t) n.
Proof.
gd h.
induction t; intros.
- cbn in H. lia.
- cbn.
  destruct n.
  1: reflexivity.
  cbn.
  apply IHt. cbn in H. lia.
Qed.


Lemma list_eq__nth_error{T}(ls1 ls2:list T):
  length ls1 = length ls2 ->
  (forall n:nat,
  n<length ls1 ->
  nth_error ls1 n = nth_error ls2 n) ->
  ls1=ls2.
Proof.
  gd ls2.
  induction ls1.
  - intros.
    destruct ls2.
    + reflexivity.
    + cbn in H. cg.
  - intros.
    destruct ls2.
    + cbn in H. cg.
    + assert (a=t) as H1. {
        assert (Some a = Some t) as H1 by (apply (H0 0); cbn; lia).
        cg.
      }
      subst. f_equal.
      cbn in H. invst H.
      eapply IHls1.
      1: assumption.
      intros.
      apply (H0 (S n)).
      cbn. lia.
Qed.


Fixpoint pop_back'{T}(x:T)(ls:list T):(list T)*T :=
  match ls with
  | nil => (nil,x)
  | h :: t => let (a,b):=pop_back' h t in (x::a,b)
  end.


Lemma pop_back'__push_back{T} (h:T) t x2:
  pop_back' h (t ++ x2 :: nil) = (h::t,x2).
Proof.
  gd h.
  induction t; intros; cbn; cg.
  rewrite IHt. reflexivity.
Qed.










Definition St_enc(x:St):positive :=
match x with
| St0 => xH
| St1 => xO xH
| St2 => xI xH
| St3 => xO (xO xH)
| St4 => xI (xO xH)
end.

Lemma St_enc_inj: is_inj St_enc.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.


Definition St_eqb(s1 s2:St) :=
match s1,s2 with
| St0,St0 | St1,St1 | St2,St2 | St3,St3 | St4,St4 => true
| _,_ => false
end.

Lemma St_eqb_spec s1 s2:
  if St_eqb s1 s2 then s1=s2 else s1<>s2.
Proof.
  destruct s1,s2; cbn; congruence.
Qed.


Ltac eq_dec eqb_spec eqb s1 s2 :=
  pose proof (eqb_spec s1 s2);
  destruct (eqb s1 s2).

Ltac St_eq_dec s1 s2 :=
  eq_dec St_eqb_spec St_eqb s1 s2.



Definition Σ_eqb(i1 i2:Σ) :=
match i1,i2 with
| Σ0,Σ0 | Σ1,Σ1 => true
| _,_ => false
end.

Lemma Σ_eqb_spec i1 i2:
  if Σ_eqb i1 i2 then i1=i2 else i1<>i2.
Proof.
  destruct i1,i2; cbn; congruence.
Qed.



Definition Σ_enc(x:Σ):positive :=
match x with
| Σ0 => xH
| Σ1 => xO xH
end.

Lemma Σ_enc_inj: is_inj Σ_enc.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.


Fixpoint listΣ_enc(x:list Σ):positive :=
match x with
| nil => xH
| Σ0::t => xO (listΣ_enc t)
| Σ1::t => xI (listΣ_enc t)
end.

Lemma listΣ_inj: is_inj listΣ_enc.
Proof.
  intros x1 x2 H.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; cbn; intros; cg.
  - destruct h2; invst H.
  - destruct h1; invst H.
  - destruct h1,h2; invst H.
    1,2: f_equal; apply IHt1,H1.
Qed.



Lemma map_inj{T1 T2}(f:T1->T2): is_inj f -> is_inj (map f).
Proof.
  intros H x1 x2 H0.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; cbn; intros; cg.
  invst H0.
  rewrite (IHt1 _ H3).
  f_equal.
  apply H,H2.
Qed.

Definition listT_enc{T}(f:T->positive)(x:list T):positive :=
  enc_list (map f x).

Lemma listT_enc_inj{T}(f:T->positive): is_inj f -> is_inj (listT_enc f).
Proof.
  intros H x1 x2 H0.
  unfold listT_enc.
  apply (map_inj _ H).
  unfold listT_enc in H0.
  apply enc_list_inj,H0.
Qed.


Definition Dir_rev(d:Dir) :=
match d with
| Dneg => Dpos
| Dpos => Dneg
end.

Definition Dir_eqb(d1 d2:Dir):bool :=
match d1,d2 with
| Dpos,Dpos | Dneg,Dneg => true
| _,_ => false
end.

Lemma Dir_eqb_spec d1 d2:
  if Dir_eqb d1 d2 then d1=d2 else d1<>d2.
Proof.
  destruct d1,d2; cbn; cg.
Qed.

Ltac Dir_eq_dec s1 s2 :=
  eq_dec Dir_eqb_spec Dir_eqb s1 s2.




Definition St_list:= St0::St1::St2::St3::St4::nil.
Definition Σ_list:= Σ0::Σ1::nil.
Definition Dir_list := Dpos::Dneg::nil.

Lemma St_list_spec:
  forall s, In s St_list.
Proof.
  intro s.
  destruct s; cbn; tauto.
Qed.

Lemma Σ_list_spec:
  forall s, In s Σ_list.
Proof.
  intro s.
  destruct s; cbn; tauto.
Qed.

Lemma Dir_list_spec:
  forall s, In s Dir_list.
Proof.
  intro s.
  destruct s; cbn; tauto.
Qed.

Definition forallb_St f :=
  forallb f St_list.

Definition forallb_Σ f :=
  forallb f Σ_list.

Definition forallb_Dir f :=
  forallb f Dir_list.

Lemma forallb_St_spec f:
  forallb_St f = true <-> forall s, f s = true.
Proof.
  unfold forallb_St.
  rewrite forallb_forall.
  split; intros.
  - apply H,St_list_spec.
  - apply H.
Qed.

Lemma forallb_Σ_spec f:
  forallb_Σ f = true <-> forall s, f s = true.
Proof.
  unfold forallb_Σ.
  rewrite forallb_forall.
  split; intros.
  - apply H,Σ_list_spec.
  - apply H.
Qed.

Lemma forallb_Dir_spec f:
  forallb_Dir f = true <-> forall s, f s = true.
Proof.
  unfold forallb_Dir.
  rewrite forallb_forall.
  split; intros.
  - apply H,Dir_list_spec.
  - apply H.
Qed.





Section TM.

Hypothesis Σ:Set.
Hypothesis Σ0:Σ.

Definition Halts(tm:TM Σ)(st:ExecState Σ): Prop :=
  exists n, HaltsAt Σ tm n st.

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
  ~HaltsAt Σ tm m st.
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
  HaltsAt Σ tm n1 st ->
  HaltsAt Σ tm n2 st ->
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
  forall (tm:TM Σ)(n0:nat), P tm -> HaltsAt Σ tm n0 st -> n0<=BB.


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
  HaltsAt Σ tm n st ->
  Steps Σ tm n st (s,t) ->
  tm0 s (t 0%Z) = None ->
  HaltsAt Σ tm0 n st.
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
  HaltsAt Σ tm n st ->
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
  HaltsAt Σ tm n st ->
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
  HaltsAt Σ tm n st ->
  HaltsAt Σ (TM_swap tm) n (ExecState_swap st).
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
  HaltsAt Σ tm n st <->
  HaltsAt Σ (TM_swap tm) n (ExecState_swap st).
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


Lemma fext_inv{A}{B} {f g:A->B}(x:A):
  f = g ->
  f x = g x.
Proof.
  cg.
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
  HaltsAt Σ tm n st ->
  HaltsAt Σ (TM_rev tm) n (ExecState_rev st).
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
  HaltsAt Σ tm n st <->
  HaltsAt Σ (TM_rev tm) n (ExecState_rev st).
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

Definition St_to_nat(x:St):nat:=
match x with
| St0 => 0
| St1 => 1
| St2 => 2
| St3 => 3
| St4 => 4
end.

Lemma St_to_nat_inj: is_inj St_to_nat.
Proof.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.

Definition St_suc(x:St):St :=
match x with
| St0 => St1
| St1 => St2
| St2 => St3
| St3 => St4
| St4 => St4
end.

Definition St_le(s1 s0:St):Prop :=
  St_to_nat s0 <= St_to_nat s1.

Lemma St_suc_le x:
  St_le (St_suc x) x.
Proof.
  unfold St_le.
  destruct x; cbn; lia.
Qed.

Lemma St_suc_eq x:
  x = (St_suc x) ->
  forall x0, St_le x x0.
Proof.
  destruct x; cbn; cg.
  intros.
  destruct x0; unfold St_le; cbn; lia.
Qed.

Lemma St_suc_neq x:
  x <> (St_suc x) ->
  St_to_nat (St_suc x) = S (St_to_nat x).
Proof.
  destruct x; cbn; cg.
Qed.


Definition UnusedState_ptr tm s1:=
  (forall s0, UnusedState tm s0 <-> St_le s0 s1) \/
  ((forall s0, ~UnusedState tm s0) /\ forall s0, St_le s1 s0).


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

Section TNF.

Fixpoint list_nat_sum(ls:list nat):nat :=
match ls with
| nil => O
| h::t => h+(list_nat_sum t)
end.

Definition isHaltTrans(tr:option (Trans Σ)):nat :=
  match tr with
  | Some _ => 0
  | None => 1
  end.

Lemma isHaltTrans_0 tr:
  isHaltTrans tr = 0 <-> tr <> None.
Proof.
  destruct tr; cbn; split; intro; cg.
Qed.

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

Ltac destruct_and :=
  match goal with
  | H:?A/\?B |- _ => destruct H
  end.

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

Definition Trans_list:=
{| nxt:=St0; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St0; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St0; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St0; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St1; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St1; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St1; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St1; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St2; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St2; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St2; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St2; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St3; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St3; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St3; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St3; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St4; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St4; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St4; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St4; dir:=Dpos; out:=Σ1 |}::
nil.

Lemma Trans_list_spec:
  forall tr, In tr Trans_list.
Proof.
  intro.
  destruct tr as [s d o].
  cbn.
  destruct s,d,o; tauto.
Qed.

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

Definition TM_simplify tm :=
  makeTM
  (tm St0 Σ0) (tm St0 Σ1)
  (tm St1 Σ0) (tm St1 Σ1)
  (tm St2 Σ0) (tm St2 Σ1)
  (tm St3 Σ0) (tm St3 Σ1)
  (tm St4 Σ0) (tm St4 Σ1).

Lemma TM_simplify_spec tm:
  TM_simplify tm = tm.
Proof.
  unfold TM_simplify,makeTM.
  fext. fext.
  destruct x,x0; reflexivity.
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

Inductive HaltDecideResult :=
| Result_Halt(s:St)(i:Σ)
| Result_NonHalt
| Result_Unknown
.

Definition HaltDecider := TM Σ -> HaltDecideResult.

Definition HaltDecider_WF(f:HaltDecider) :=
  forall tm,
    match f tm with
    | Result_Halt s i => exists n t, HaltsAt _ tm n (InitES Σ Σ0) /\ Steps _ tm n (InitES Σ Σ0) (s,t) /\ t Z0 = i /\ n<=BB
    | Result_NonHalt => ~HaltsFromInit Σ Σ0 tm
    | Result_Unknown => True
    end.

Definition HaltDecider_cons(f g:HaltDecider):HaltDecider :=
  fun tm =>
    let res := f tm in
      match res with
      | Result_Unknown => g tm
      | _ => res
      end.

Lemma HaltDecider_cons_spec(f g:HaltDecider):
  HaltDecider_WF f ->
  HaltDecider_WF g ->
  HaltDecider_WF (HaltDecider_cons f g).
Proof.
  intros Hf Hg tm.
  specialize (Hf tm).
  specialize (Hg tm).
  unfold HaltDecider_cons.
  destruct (f tm); auto 1.
Qed.

Definition HaltDecider_nil:HaltDecider := fun _ => Result_Unknown.

Fixpoint HaltDecider_list(f:list HaltDecider):HaltDecider :=
  match f with
  | nil => HaltDecider_nil
  | h::t => HaltDecider_cons h (HaltDecider_list t)
  end.

Definition SearchQueue :=
  ((list TNF_Node)*(list TNF_Node))%type.

Definition SearchQueue_WF (q:SearchQueue) x0:=
  let (q1,q2):=q in
  (forall x, In x (q1++q2) -> TNF_Node_WF x) /\
  ((forall x, In x (q1++q2) -> TNF_Node_HTUB x) -> TNF_Node_HTUB x0).

Definition SearchQueue_upd(q:SearchQueue)(f:HaltDecider) :=
  match q with
  | (h::t,q2) =>
    match f (TNF_tm h) with
    | Result_Halt s i => ((TNF_Node_expand h s i)++t,q2)
    | Result_NonHalt => (t,q2)
    | Result_Unknown => (t,h::q2)
    end
  | _ => q
  end.

Lemma SearchQueue_upd_spec {q x0 f}:
  SearchQueue_WF q x0 ->
  HaltDecider_WF f ->
  SearchQueue_WF (SearchQueue_upd q f) x0.
Proof.
  destruct q as [q1 q2].
  destruct q1 as [|h q1].
  1: tauto.
  cbn.
  intros Hq Hf.
  destruct Hq as [Hq1 Hq2].
  specialize (Hf (TNF_tm h)).
  destruct (f (TNF_tm h)).
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

Definition SearchQueue_upd_bfs(q:SearchQueue)(f:HaltDecider) :=
  match q with
  | (h::t,q2) =>
    match f (TNF_tm h) with
    | Result_Halt s i => (t,(TNF_Node_expand h s i)++q2)
    | Result_NonHalt => (t,q2)
    | Result_Unknown => (t,h::q2)
    end
  | _ => q
  end.


Lemma SearchQueue_upd_bfs_spec {q x0 f}:
  SearchQueue_WF q x0 ->
  HaltDecider_WF f ->
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
  destruct (f (TNF_tm h)); auto 1.
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
  HaltDecider_WF f ->
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
  HaltDecider_WF f ->
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
  HaltDecider_WF f ->
  SearchQueue_WF (SearchQueue_bfs q f) x0.
Proof.
  intros.
  unfold SearchQueue_bfs.
  apply SearchQueue_reset_spec.
  apply SearchQueue_upds_bfs_spec; auto 1.
Qed.

Definition root := {| TNF_tm:=TM0; TNF_cnt:=CountHaltTrans (TM0); TNF_ptr:=St1 |}.

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

Definition root_q := SearchQueue_init root.

End TNF.

Section CPS.

Hypothesis Σ:Set.

Hypothesis T:Type.
Hypothesis InT:(ExecState Σ)->T->Prop.

Definition isClosed(tm:TM Σ)(S:T):Prop :=
  forall st0,
  InT st0 S ->
  exists n,
  exists st1,
  Steps Σ tm (1+n) st0 st1 /\
  InT st1 S.



Lemma Closed_NonHalt tm S st:
  InT st S ->
  isClosed tm S ->
  forall n:nat,
  exists m:nat,
  n<=m /\
  exists st0,
  Steps Σ tm m st st0 /\
  InT st0 S.
Proof.
  intros H H0 n.
  induction n.
  - exists 0.
    split.
    1: lia.
    exists st.
    split.
    2: assumption.
    ctor.
  - destruct IHn as [m [H1 [st0 [H2 H3]]]].
    destruct (H0 _ H3) as [n0 [st1 [H4 H5]]].
    pose proof (Steps_trans _ H2 H4) as H6.
    exists (1+n0+m).
    split.
    1: lia.
    exists st1.
    tauto.
Qed.



Lemma CPS_correct tm S st:
  InT st S ->
  isClosed tm S ->
  ~Halts _ tm st.
Proof.
  intros.
  unfold Halts.
  intro H1.
  destruct H1 as [n H1].
  destruct (Closed_NonHalt _ _ _ H H0 (1+n)) as [m [H2 [st0 [H3 H4]]]].
  assert (H5:n<m) by lia.
  apply (Steps_NonHalt _ H5 H3 H1).
Qed.


End CPS.




Section NGramCPS.

Hypothesis Σ:Set.
Hypothesis len_l:nat.
Hypothesis len_r:nat.

Record MidWord:Set := {
  l:list Σ;
  r:list Σ;
  m:Σ;
  s:St;
}.

Fixpoint tape_seg(t:Z->Σ)(x:Z)(d:Dir)(n:nat):list Σ :=
  match n with
  | O => nil
  | S n0 => (t x)::(tape_seg t (x+(Dir_to_Z d))%Z d n0)
  end.



Definition MidWord_matches(st:ExecState Σ)(mw:MidWord):Prop :=
  let (s,t) := st in
  let (l0,r0,m0,s0):=mw in
  s = s0 /\
  m0 = t Z0 /\
  l0 = tape_seg t ((-1)%Z) Dneg len_l /\
  r0 = tape_seg t (1%Z) Dpos len_r.

Record AbstractES:Type := {
  lset: (list Σ)->Prop;
  rset: (list Σ)->Prop;
  mset: MidWord->Prop;
}.

Definition xset_matches(t:Z->Σ)(xs:(list Σ)->Prop)(d:Dir)(len:nat):Prop :=
  forall n:nat,
  1<n ->
  exists ls,
  xs ls /\
  ls = tape_seg t ((Z.of_nat n)*(Dir_to_Z d)%Z) d len.


Definition InAES(st:ExecState Σ)(S:AbstractES):Prop :=
  let (s,t) := st in
  let (ls,rs,ms) := S in
  (exists mw, ms mw /\ MidWord_matches st mw) /\
  xset_matches t ls Dneg len_l /\
  xset_matches t rs Dpos len_r.


Definition AES_isClosed(tm:TM Σ)(S:AbstractES):Prop :=
  forall st0,
  InAES st0 S ->
  exists st1,
  step Σ tm st0 = Some st1 /\
  InAES st1 S.

Lemma AES_Closed_NonHalt tm S st:
  InAES st S ->
  AES_isClosed tm S ->
  ~Halts _ tm st.
Proof.
  intros.
  eapply CPS_correct.
  1: apply H.
  unfold isClosed.
  unfold AES_isClosed in H0.
  intros st0 H1.
  specialize (H0 st0 H1).
  destruct H0 as [st1 [H0a H0b]].
  exists 0.
  exists st1.
  split. 2: assumption.
  cbn.
  ector.
  - ector.
  - assumption.
Qed.


Definition AES_CloseAt(tm:TM Σ)(S:AbstractES)(mw:MidWord):Prop :=
  let (ls,rs,ms) := S in
  let (l0,r0,m0,s0):=mw in
  match l0,r0 with
  | hl::l1,hr::r1 =>
    match tm s0 m0 with
    | Some tr =>
    let (s1,d,o):=tr in
      match d with
      | Dpos => 
        ls l0 /\
        forall x:Σ, rs (r1++(x::nil)) ->
        ms {|
          l:=o::(pop_back hl l1);
          m:=hr;
          r:=r1++(x::nil);
          s:=s1;
        |}
      | Dneg =>
        rs r0 /\
        forall x:Σ, ls (l1++(x::nil)) ->
        ms {|
          r:=o::(pop_back hr r1);
          m:=hl;
          l:=l1++(x::nil);
          s:=s1;
        |}
      end
    | _ => False
    end
  | _,_ => False
  end.


Definition AES_isClosed'(tm:TM Σ)(S:AbstractES):Prop :=
  let (ls,rs,ms) := S in
  forall mw,
  ms mw ->
  AES_CloseAt tm S mw.


Lemma tape_seg_hd h t1 t x d len:
  h :: t1 = tape_seg t x d len ->
  h = t x.
Proof.
  destruct len.
  - cbn. intro. cg.
  - cbn. intro.
    invst H. cg. 
Qed.

Lemma tape_seg_spec t x d len:
  (forall n:nat,
  n<len ->
  nth_error (tape_seg t x d len) n = Some (t (x+(Dir_to_Z d)*(Z.of_nat n))%Z))/\
  length (tape_seg t x d len) = len.
Proof.
  split.
  {
    gd x.
    induction len.
    1: lia.
    intros.
    destruct n.
    - cbn. repeat f_equal. lia.
    - assert (H0:n<len) by lia.
      cbn.
      rewrite (IHlen (x+(Dir_to_Z d))%Z n H0).
      f_equal; f_equal. lia.
  }
  {
    gd x.
    induction len.
    - intros. reflexivity.
    - intros. cbn.
      f_equal.
      apply IHlen.
  }
Qed.

Lemma tape_seg_pop hl l1 t d len:
  hl :: l1 = tape_seg t (Dir_to_Z d) d len ->
  (l1 ++ t ((Dir_to_Z d)*(Z.of_nat (S len)))%Z :: nil) = (tape_seg t ((Dir_to_Z d)*2)%Z d len).
Proof.
  intro H.
  destruct (tape_seg_spec t (Dir_to_Z d) d len) as [H0a H0b].
  destruct (tape_seg_spec t (Dir_to_Z d * 2) d len) as [H1a H1b].
  rewrite <-H in H0a,H0b.
  destruct len.
  1: cbn in H0b; cg.
  cbn in H0b.
  injection H0b; intro.
  apply list_eq__nth_error.
  - rewrite H1b.
    rewrite app_length,H0. cbn.
    lia.
  - rewrite app_length,H0.
    intros.
    cbn in H1.
    assert (n<length l1 \/ n=length l1) by lia.
    destruct H2 as [H2|H2].
    + rewrite nth_error_app1. 2: assumption.
      specialize (H0a (S n)). cbn in H0a.
      rewrite H0a. 2: lia.
      specialize (H1a n).
      rewrite H1a. 2: lia.
      f_equal. f_equal. lia.
    + rewrite nth_error_app2. 2: lia.
      assert (H3:n-length l1 = 0) by lia.
      rewrite H3.
      specialize (H1a n).
      rewrite H1a. 2: lia.
      cbn.
      f_equal. f_equal. lia.
Qed.

Lemma tape_seg_mov_upd t d o len:
  tape_seg t ((Dir_to_Z d)*2)%Z d len = tape_seg (mov Σ (upd Σ t o) d) (Dir_to_Z d) d len.
Proof.
  destruct (tape_seg_spec t (Dir_to_Z d * 2) d len) as [H0a H0b].
  destruct (tape_seg_spec (mov Σ (upd Σ t o) d) (Dir_to_Z d) d len) as [H1a H1b].
  apply list_eq__nth_error.
  1: cg.
  intros.
  rewrite (H0a n). 2: lia.
  rewrite (H1a n). 2: lia.
  f_equal.
  unfold mov,upd.
  assert ((Dir_to_Z d + Dir_to_Z d * Z.of_nat n + Dir_to_Z d <> 0)%Z). {
    destruct d;
    unfold Dir_to_Z; lia.
  }
  rewrite <-Z.eqb_neq in H0.
  rewrite H0.
  f_equal. lia.
Qed.
  

Lemma tape_seg_mov_upd_2 hr r1 t d o len:
  hr :: r1 = tape_seg t (Dir_to_Z d) d len ->
  o :: pop_back hr r1 = tape_seg (mov Σ (upd Σ t o) (Dir_rev d)) (Dir_to_Z d) d len.
Proof.
intros.
  destruct (tape_seg_spec t (Dir_to_Z d) d len) as [H0a H0b].
  destruct (tape_seg_spec (mov Σ (upd Σ t o) (Dir_rev d)) (Dir_to_Z d) d len) as [H1a H1b].
  assert (H':length (o::pop_back hr r1) = len). {
    cbn. rewrite pop_back_len.
    rewrite <-H in H0b.
    destruct len; cbn in H0b; cg.
  }
  apply list_eq__nth_error.
  1: cg.
  rewrite H'.
  intros.
  rewrite H1a. 2: lia.
  destruct n.
  - cbn. f_equal.
    unfold mov,upd.
    destruct d; cbn; reflexivity.
  - cbn. cbn in H'.
    destruct len. 1: lia.
    rewrite <-H in H0a,H0b.
    cbn in H0b.
    rewrite pop_back__nth_error. 2: lia.
    rewrite H0a. 2: lia.
    unfold mov,upd.
    f_equal.
    assert (H2:(Dir_to_Z d + Dir_to_Z d * Z.pos (Pos.of_succ_nat n) + Dir_to_Z (Dir_rev d) <> 0)%Z). {
      destruct d; unfold Dir_rev,Dir_to_Z; lia.
    }
    rewrite <-Z.eqb_neq in H2.
    rewrite H2.
    f_equal.
    assert (H1:(Z.pos (Pos.of_succ_nat n) = 1+(Z.of_nat n))%Z) by lia.
    rewrite H1.
    destruct d; unfold Dir_to_Z,Dir_rev; lia.
Qed.

Lemma xset_matches_mov_upd_1 t ls d o len:
  xset_matches t ls d len ->
  xset_matches (mov Σ (upd Σ t o) d) ls d len.
Proof.
  unfold xset_matches.
  intros.
  assert (1<1+n) as H1 by lia.
  specialize (H (1+n) H1).
  destruct H as [ls0 [Ha Hb]].
  exists ls0.
  split. 1: assumption.
  rewrite Hb.

  destruct (tape_seg_spec t (Z.of_nat (1 + n) * Dir_to_Z d) d len) as [H0a H0b].
  destruct (tape_seg_spec (mov Σ (upd Σ t o) d) (Z.of_nat n * Dir_to_Z d) d len) as [H1a H1b].
  apply list_eq__nth_error.
  1: lia.
  rewrite H0b.
  intros.
  rewrite H0a. 2: assumption.
  rewrite H1a. 2: assumption.
  f_equal.
  unfold mov,upd.
  assert (H2:(Z.of_nat n * Dir_to_Z d + Dir_to_Z d * Z.of_nat n0 + Dir_to_Z d <> 0)%Z). {
    destruct d; unfold Dir_to_Z; lia.
  }
  rewrite <-Z.eqb_neq in H2.
  rewrite H2.
  f_equal. lia.
Qed.

Lemma xset_matches_mov_upd_2 t rs d o len:
  xset_matches t rs d len ->
  rs (tape_seg t (Dir_to_Z d) d len) ->
  xset_matches (mov Σ (upd Σ t o) (Dir_rev d)) rs d len.
Proof.
  unfold xset_matches.
  intros.
  destruct n. 1: lia.
  assert (H2:1<n\/n=1) by lia.
  destruct H2 as [H2|H2].
  - specialize (H n H2).
    destruct H as [ls [Ha Hb]].
    exists ls.
    split. 1: assumption.
    rewrite Hb.

    destruct (tape_seg_spec t (Z.of_nat n * Dir_to_Z d) d len) as [H0a H0b].
    destruct (tape_seg_spec (mov Σ (upd Σ t o) (Dir_rev d)) (Z.of_nat (S n) * Dir_to_Z d) d len) as [H1a H1b].
    apply list_eq__nth_error.
    1: lia.
    rewrite H0b.
    intros.
    rewrite H0a. 2: lia.
    rewrite H1a. 2: lia.
    f_equal.
    unfold mov,upd.
    assert (H3:(Z.of_nat (S n) * Dir_to_Z d + Dir_to_Z d * Z.of_nat n0 + Dir_to_Z (Dir_rev d) <> 0)%Z) by
      (destruct d; unfold Dir_to_Z,Dir_rev; lia).
    rewrite <-Z.eqb_neq in H3.
    rewrite H3.
    f_equal.
    destruct d; unfold Dir_to_Z,Dir_rev; lia.
  - eexists.
    split. 1: apply H0.
    subst.

    destruct (tape_seg_spec t (Dir_to_Z d) d len) as [H0a H0b].
    destruct (tape_seg_spec (mov Σ (upd Σ t o) (Dir_rev d)) (Z.of_nat 2 * Dir_to_Z d) d len) as [H1a H1b].
    apply list_eq__nth_error.
    1: lia.
    rewrite H0b.
    intros.
    rewrite H0a. 2: lia.
    rewrite H1a. 2: lia.
    f_equal.
    unfold mov,upd.
    assert (H3:((Z.of_nat 2 * Dir_to_Z d + Dir_to_Z d * Z.of_nat n + Dir_to_Z (Dir_rev d) <> 0))%Z) by
      (destruct d; unfold Dir_to_Z,Dir_rev; lia).
    rewrite <-Z.eqb_neq in H3.
    rewrite H3.
    f_equal.
    destruct d; unfold Dir_to_Z,Dir_rev; lia.
Qed.



Lemma AES_isClosed'_correct tm S:
  AES_isClosed' tm S ->
  AES_isClosed tm S.
Proof.
  destruct S.
  unfold AES_isClosed',AES_isClosed,AES_CloseAt.
  intros H st0 H0.
  unfold InAES in H0.
  destruct st0 as [s t].
  destruct H0 as [[mw [H0a H0b]] [H0c H0d]].
  specialize (H mw H0a).
  destruct mw.
  destruct l0 as [|hl l1]. 1: contradiction.
  destruct r0 as [|hr r1]. 1: contradiction.
  destruct (tm s0 m0) as [[s1 d o]|] eqn:E.
  2: contradiction.
  unfold MidWord_matches in H0b.
  destruct H0b as [H1a [H1b [H1c H1d]]].
  subst.
  cbn.
  rewrite E.
  eexists.
  split.
  1: reflexivity.
  unfold InAES.

  destruct d.
  {
    destruct H as [Ha Hb].
    pose proof (H0c 2) as H2.
    cbn in H2.
    assert (H3:1<2) by lia.
    specialize (H2 H3).
    destruct H2 as [ls [H2a H2b]].
    subst.
    specialize (Hb (t (-1-(Z.of_nat len_l))%Z)).
    split.
    - exists
     {|
       l := l1 ++ t (-1 - Z.of_nat len_l)%Z :: nil;
       r := o :: pop_back hr r1;
       m := hl;
       s := s1
     |}.
      assert (H':(l1 ++ t (-1 - Z.of_nat len_l)%Z :: nil)=(tape_seg t (-2) Dneg len_l)). {
        pose proof (tape_seg_pop _ _ _ Dneg _ H1c) as H4.
        cbn in H4.
        rewrite <-H4 in H2a.
        assert (H5:(Z.neg (Pos.of_succ_nat len_l))=(-1 - Z.of_nat len_l)%Z) by lia.
        rewrite <-H5.
        apply H4.
      }
      split.
      + apply Hb.
        rewrite H'; assumption.
      + unfold MidWord_matches.
        repeat split; auto.
        * cbn.
          eapply tape_seg_hd. apply H1c.
        * rewrite H'.
          apply (tape_seg_mov_upd _ Dneg _ _).
        * apply (tape_seg_mov_upd_2 _ _ _ Dpos _ _ H1d).
    - split.
      + apply xset_matches_mov_upd_1; assumption.
      + rewrite H1d in Ha.
        eapply (xset_matches_mov_upd_2 _ _ Dpos _ _); eassumption.
  }
  {
    destruct H as [Ha Hb].
    pose proof (H0d 2) as H2.
    cbn in H2.
    assert (H3:1<2) by lia.
    specialize (H2 H3).
    destruct H2 as [ls [H2a H2b]].
    subst.
    specialize (Hb (t (1+(Z.of_nat len_r))%Z)).
    split.
    - exists
       {|
         l := o :: pop_back hl l1;
         r := r1 ++ t (1 + Z.of_nat len_r)%Z :: nil;
         m := hr;
         s := s1
       |}.
      assert (H':(r1 ++ t (1 + Z.of_nat len_r)%Z :: nil)=(tape_seg t (2) Dpos len_r)). {
        pose proof (tape_seg_pop _ _ _ Dpos _ H1d) as H4.
        cbn in H4.
        rewrite <-H4 in H2a.
        assert (H5:(Z.pos (Pos.of_succ_nat len_r))=(1 + Z.of_nat len_r)%Z) by lia.
        rewrite <-H5.
        apply H4.
      }
      split.
      + apply Hb.
        rewrite H'; assumption.
      + unfold MidWord_matches.
        repeat split; auto.
        * cbn.
          eapply tape_seg_hd. apply H1d.
        * apply (tape_seg_mov_upd_2 _ _ _ Dneg _ _ H1c).
        * rewrite H'.
          apply (tape_seg_mov_upd _ Dpos _ _).
    - split.
      + rewrite H1c in Ha.
        eapply (xset_matches_mov_upd_2 _ _ Dneg _ _); eassumption.
      + apply xset_matches_mov_upd_1; assumption.
  }
Qed.

Hypothesis Σ_enc: Σ->positive.
Hypothesis Σ_enc_inj: is_inj Σ_enc.
Hypothesis listΣ_enc: (list Σ)->positive.
Hypothesis listΣ_enc_inj: is_inj listΣ_enc.





Definition MidWord_enc(mw:MidWord):positive :=
  let (l,r,m,s):=mw in
  enc_list ((St_enc s)::(Σ_enc m)::(listΣ_enc l)::(listΣ_enc r)::nil).

Lemma MidWord_enc_inj: is_inj MidWord_enc.
Proof.
  intros x1 x2 H.
  destruct x1 as [l1 r1 m1 s1].
  destruct x2 as [l2 r2 m2 s2].
  unfold MidWord_enc in H.
  pose proof (enc_list_inj _ _ H). clear H.
  invst H0.
  rewrite (St_enc_inj _ _ H1).
  rewrite (Σ_enc_inj _ _ H2).
  rewrite (listΣ_enc_inj _ _ H3).
  rewrite (listΣ_enc_inj _ _ H4).
  reflexivity.
Qed.

Definition xset_impl:Type := (PositiveMap.tree ((list Σ)*(PositiveMap.tree unit))).
Definition mset_impl:Type := (list MidWord)*(PositiveMap.tree unit).





Definition xset_in(xs:xset_impl)(x:list Σ):Prop :=
  match x with
  | h::t =>
    let (x1,x2):=pop_back' h t in
    match PositiveMap.find (listΣ_enc x1) xs with
    | Some v =>
      set_in Σ_enc v x2
    | None => False
    end
  | nil => False
  end.

Definition xset_ins0(xs:xset_impl)(v:(list Σ)*(PositiveMap.tree unit))(x1:list Σ)(x2:Σ):xset_impl*bool :=
  let (v',flag):=(set_ins Σ_enc v x2) in
  (PositiveMap.add (listΣ_enc x1) v' xs, flag).

Definition xset_ins(xs:xset_impl)(x:list Σ):xset_impl*bool :=
  match x with
  | h::t =>
    let (x1,x2):=pop_back' h t in
    match PositiveMap.find (listΣ_enc x1) xs with
    | Some v =>
      xset_ins0 xs v x1 x2
    | None =>
      xset_ins0 xs (nil, PositiveMap.empty unit) x1 x2
    end
  | nil => (xs,false)
  end.

Definition xset_as_list(xs:xset_impl)(x1:list Σ):list Σ :=
  match PositiveMap.find (listΣ_enc x1) xs with
  | Some v => fst v
  | None => nil
  end.

Definition xset_WF(xs:xset_impl):Prop :=
  forall (x1:list Σ)(x2:Σ),
    xset_in xs (x1++x2::nil) <->
    match PositiveMap.find (listΣ_enc x1) xs with
    | Some v =>
      In x2 (fst v)
    | None => False
    end.


Definition mset_in(ms:mset_impl)(x:MidWord):Prop := set_in MidWord_enc ms x.

Definition mset_WF(ms:mset_impl):Prop :=
  set_WF MidWord_enc ms.

Definition mset_ins0(ms:mset_impl)(mw:MidWord):mset_impl*bool :=
  set_ins MidWord_enc ms mw.

Lemma mset_ins0_spec ms mw ms' flag:
  mset_WF ms ->
  mset_ins0 ms mw = (ms',flag) ->
  (mset_WF ms' /\
  (flag=true -> (ms'=ms /\ mset_in ms mw))).
Proof.
  apply set_ins_spec.
  unfold is_inj.
  intros.
  apply MidWord_enc_inj,H.
Qed.


Fixpoint mset_ins(q:list MidWord)(ms:mset_impl)(flag:bool)(f:Σ->MidWord)(ls:list Σ):((list MidWord)*mset_impl)*bool :=
  match ls with
  | nil => ((q,ms),flag)
  | h::t =>
    let (ms',flag'):=mset_ins0 ms (f h) in
    let q' := if flag' then q else ((f h)::q) in
    mset_ins q' ms' (andb flag flag') f t
  end.






Record AES_impl := {
  lset': xset_impl;
  rset': xset_impl;
  mset': mset_impl;
}.


Definition AES_impl_to_AES(x:AES_impl):AbstractES :=
  let (ls,rs,ms):=x in
  {|
    lset := xset_in ls;
    rset := xset_in rs;
    mset := mset_in ms;
  |}.

Definition AES_impl_WF(x:AES_impl):Prop :=
  let (ls,rs,ms):=x in
  xset_WF ls /\
  xset_WF rs /\
  mset_WF ms.

Definition update_AES_MidWord(tm:TM Σ)(q:list MidWord)(mw:MidWord)(SI:AES_impl):((list MidWord)*AES_impl)*bool :=
let (l0,r0,m0,s0):=mw in
let (ls,rs,ms):=SI in
  match l0,r0 with
  | hl::l1,hr::r1 =>
    match tm s0 m0 with
    | Some tr =>
      let (s1,d,o):=tr in
      match d with
      | Dpos =>
        let (ls',flag1):= xset_ins ls l0 in
        match
          mset_ins q ms true
            (fun x => {|
              l:=o::(pop_back hl l1);
              m:=hr;
              r:=r1++(x::nil);
              s:=s1;
            |}) (xset_as_list rs r1)
        with (q',ms',flag2) =>
          ((q',{| lset':=ls'; rset':=rs; mset':=ms' |}), andb flag1 flag2)
        end
      | Dneg =>
        let (rs',flag1):= xset_ins rs r0 in
        match
          mset_ins q ms true
            (fun x => {|
              r:=o::(pop_back hr r1);
              m:=hl;
              l:=l1++(x::nil);
              s:=s1;
            |}) (xset_as_list ls l1)
        with (q',ms',flag2) =>
          ((q',{| lset':=ls; rset':=rs'; mset':=ms' |}), andb flag1 flag2)
        end
      end
    | _ => ((q,SI),false)
    end
  | _,_ => ((q,SI),false)
  end.


Fixpoint update_AES(tm:TM Σ)(ms:list MidWord)(SI:AES_impl)(flag:bool)(n:nat):AES_impl*bool*nat :=
  match n with
  | O => (SI,false,O)
  | S n0 =>
    match ms with
    | nil => (SI,flag,n0)
    | mw::ms0 =>
      let (S',flag'):=update_AES_MidWord tm ms0 mw SI in
      let (q',SI'):=S' in
      update_AES tm q' SI' (andb flag flag') n0
    end
  end.


Lemma xset_WF_1 xs x1 v:
  xset_WF xs ->
  PositiveMap.find (listΣ_enc x1) xs = Some v ->
  set_WF Σ_enc v.
Proof.
  unfold xset_WF.
  intros.
  unfold xset_in in H.
  unfold set_WF.
  intro x2.
  specialize (H x1 x2).
  destruct x1 as [|h t]; cbn in H.
  2: rewrite pop_back'__push_back in H.
  1,2: rewrite H0 in H; apply H.
Qed.

Lemma xset_WF_2 xs x1 v':
  xset_WF xs ->
  set_WF Σ_enc v' ->
  xset_WF (PositiveMap.add (listΣ_enc x1) v' xs).
Proof.
  unfold xset_WF,xset_in,set_WF.
  intros.
  destruct x0 as [|h t]; cbn.
  - specialize (H nil x2).
    cbn in H.
    rewrite PositiveMapAdditionalFacts.gsspec.
    destruct (PositiveMap.E.eq_dec (listΣ_enc nil)); auto 1.
  - rewrite pop_back'__push_back.
    specialize (H (h::t) x2).
    cbn in H.
    rewrite pop_back'__push_back in H.
    rewrite PositiveMapAdditionalFacts.gsspec.
    destruct (PositiveMap.E.eq_dec (listΣ_enc (h :: t))); auto 1.
Qed.



Lemma xset_ins_spec xs h t xs' flag:
  xset_WF xs ->
  xset_ins xs (h :: t) = (xs', flag) ->
  (xset_WF xs' /\
  (flag=true -> (xs'=xs /\ xset_in xs (h :: t)))).
Proof.
  intros.
  cbn in H0.
  destruct (pop_back' h t) as [x1 x2] eqn:E.
  destruct (PositiveMap.find (listΣ_enc x1) xs) as [v|] eqn:E0.
  - unfold xset_ins0 in H0.
    destruct (set_ins Σ_enc v x2) as [v' flag0] eqn:E1.
    invst H0. clear H0.
    assert (W0:set_WF Σ_enc v). {
      eapply xset_WF_1.
      + apply H.
      + apply E0.
    }
    destruct (set_ins_spec _ Σ_enc_inj _ _ _ _ W0 E1) as [H0a H0b].
    split.
    1: apply xset_WF_2; assumption.
    intro; subst.
    specialize (H0b eq_refl).
    destruct H0b; subst.
    split.
    1: apply PositiveMapAdditionalFacts.gsident,E0.
    cbn. rewrite E,E0. assumption.
  - unfold xset_ins0 in H0.
    destruct (set_ins Σ_enc (nil, PositiveMap.empty unit)) as [v' flag0] eqn:E1.
    invst H0. clear H0.
    destruct (set_ins_spec _ Σ_enc_inj _ _ _ _ (empty_set_WF Σ_enc) E1) as [H0a H0b].
    split.
    1: apply xset_WF_2; assumption.
    intro; subst.
    specialize (H0b eq_refl).
    destruct H0b; subst.
    unfold set_ins in E1.
    cbn in E1. rewrite PositiveMap.gempty in E1. invst E1.
Qed.




Lemma mset_ins_spec q ms flag f ls q' ms' flag2:
  mset_WF ms ->
  mset_ins q ms flag f ls = (q',ms',flag2) ->
  (mset_WF ms' /\
  (flag2=true -> (flag=true /\ q'=q /\ ms'=ms /\
  (forall x2, In x2 ls -> mset_in ms (f x2))))).
Proof.
gd flag2. gd ms'. gd q'. gd flag. gd ms. gd q.
induction ls; intros.
- cbn in H0. invst H0.
  split. 1: assumption.
  intro H1.
  repeat split; auto 1.
  intros x2 H2.
  destruct H2.
- cbn in H0.
  destruct (mset_ins0 ms (f a)) as [ms'0 flag'] eqn:E.
  destruct (mset_ins0_spec _ _ _ _ H E) as [H1a H1b].
  specialize (IHls _ _ _ _ _ _ H1a H0).
  destruct IHls as [H2a H2b].
  split. 1: assumption.
  intro; subst.
  specialize (H2b eq_refl).
  destruct H2b as [H2b [H2c [H2d H2e]]].
  rewrite Bool.andb_true_iff in H2b.
  destruct H2b.
  subst.
  specialize (H1b eq_refl).
  destruct H1b as [H1b H1c].
  subst.
  repeat split; cg.
  intros x2 H3.
  cbn in H3.
  destruct H3 as [H3|H3]; subst; auto.
Qed.

Lemma xset_as_list_spec xs x1 x2:
  xset_WF xs ->
  xset_in xs (x1 ++ x2 :: nil) ->
  In x2 (xset_as_list xs x1).
Proof.
  intros.
  unfold xset_WF in H.
  unfold xset_in in H0.
  unfold xset_as_list.
  destruct x1 as [|h t].
  - specialize (H nil x2).
    assert (H1:nil++x2::nil = (x2::nil)) by reflexivity.
    rewrite H1 in H,H0.
    unfold pop_back' in H0.
    destruct (PositiveMap.find (listΣ_enc nil) xs) as [v|] eqn:E.
    2: contradiction.
    rewrite <-H.
    unfold xset_in.
    unfold pop_back'.
    rewrite E.
    apply H0.
  - specialize (H (h::t) x2).
    assert (H1:(h::t)++x2::nil = h::(t++x2::nil)) by reflexivity.
    rewrite H1 in H,H0.
    rewrite pop_back'__push_back in H0.
    destruct (PositiveMap.find (listΣ_enc (h :: t)) xs) as [v|] eqn:E.
    2: contradiction.
    rewrite <-H.
    cbn.
    rewrite pop_back'__push_back,E.
    apply H0.
Qed.


Lemma update_AES_MidWord_spec tm q mw SI:
  AES_impl_WF SI ->
  match update_AES_MidWord tm q mw SI with
  | (q',SI',flag) =>
    AES_impl_WF SI' /\
    (flag=true -> (q'=q /\ SI'=SI /\ AES_CloseAt tm (AES_impl_to_AES SI) mw))
  end.
Proof.
  destruct (update_AES_MidWord tm q mw SI) as [[q' SI'] flag] eqn:E.
  intros.
  destruct mw as [l0 r0 m0 s0].
  destruct SI as [ls rs ms].
  cbn in E.
  destruct l0 as [|hl l1].
  1: invst E; split; [assumption | intro; cg].
  destruct r0 as [|hr r1].
  1: invst E; split; [assumption | intro; cg].

  destruct (tm s0 m0) as [[s1 d o]|] eqn:E0.
  2: invst E; split; [assumption | intro; cg].
  destruct H as [H [H0 H1]].
  destruct d.
  {
    destruct (xset_ins rs (hr :: r1)) as [rs' flag1] eqn:E1.
    destruct
     (mset_ins q ms true
       (fun x : Σ => {| l := l1 ++ x :: nil; r := o :: pop_back hr r1; m := hl; s := s1 |})
       (xset_as_list ls l1)) as [[q'0 ms'] flag2] eqn:E2.
    invst E. clear E.
    rewrite Bool.andb_true_iff.
    destruct (xset_ins_spec _ _ _ _ _ H0 E1) as [H2a H2b].
    destruct (mset_ins_spec _ _ _ _ _ _ _ _ H1 E2) as [H3a H3b].
    unfold AES_impl_WF.
    split.
    1: tauto.
    intro H2.
    destruct H2; subst.
    specialize (H2b eq_refl).
    specialize (H3b eq_refl).
    destruct H2b as [H2b H2c].
    destruct H3b as [_ [H3b [H3c H3d]]].
    subst.
    repeat split; cg.
    unfold AES_CloseAt,AES_impl_to_AES.
    rewrite E0.
    split. 1: assumption.
    intros x H2.
    apply H3d.
    apply xset_as_list_spec; assumption.
  }
  {
    destruct (xset_ins ls (hl :: l1)) as [ls' flag1] eqn:E1.
    destruct
     (mset_ins q ms true
       (fun x : Σ => {| l := o :: pop_back hl l1; r := r1 ++ x :: nil; m := hr; s := s1 |})
       (xset_as_list rs r1)) as [[q'0 ms'] flag2] eqn:E2.
    invst E. clear E.
    rewrite Bool.andb_true_iff.
    destruct (xset_ins_spec _ _ _ _ _ H E1) as [H2a H2b].
    destruct (mset_ins_spec _ _ _ _ _ _ _ _ H1 E2) as [H3a H3b].
    unfold AES_impl_WF.
    split.
    1: tauto.
    intro H2.
    destruct H2; subst.
    specialize (H2b eq_refl).
    specialize (H3b eq_refl).
    destruct H2b as [H2b H2c].
    destruct H3b as [_ [H3b [H3c H3d]]].
    subst.
    repeat split; cg.
    unfold AES_CloseAt,AES_impl_to_AES.
    rewrite E0.
    split. 1: assumption.
    intros x H2.
    apply H3d.
    apply xset_as_list_spec; assumption.
  }
Qed.



Lemma update_AES_spec tm q SI flag n:
  AES_impl_WF SI ->
  match update_AES tm q SI flag n with
  | (SI',flag',_) =>
    AES_impl_WF SI' /\
    (flag'=true ->
      flag=true /\
      (forall mw, In mw q -> AES_CloseAt tm (AES_impl_to_AES SI) mw) /\
      SI=SI')
  end.
Proof.
  gd flag.
  gd SI.
  gd q.
  induction n; intros.
  - cbn.
    split; cg.
  - cbn.
    destruct q as [|mw q].
    + split; cg. intros. repeat split; cg.
      intros.
      destruct H1.
    + cbn.
      destruct (update_AES_MidWord tm q mw SI) as [[q' SI'] flag'] eqn:E.
      specialize (IHn q' SI' (flag&&flag')%bool).
      destruct (update_AES tm q' SI' (flag && flag') n) as [[SI'0 flag'0] n0_] eqn:E0.
      pose proof (update_AES_MidWord_spec tm q mw SI H) as Hmw.
      rewrite E in Hmw.
      destruct Hmw as [Hmw0 Hmw1].
      destruct (IHn Hmw0) as [IHn0 IHn1]. clear IHn.
      split. 1: assumption.
      intros H1.
      destruct (IHn1 H1) as [IHn1a [IHn1b IHn1d]]. clear IHn1.
      rewrite Bool.andb_true_iff in IHn1a.
      destruct IHn1a as [IHn1a IHn1c].
      repeat split. 1: cg.
      * intros mw0 H2.
        specialize (IHn1b mw0).
        specialize (Hmw1 IHn1c).
        destruct Hmw1 as [Hmw1 [Hmw2 Hmw3]]; subst.
        destruct H2 as [H2|H2]; subst; tauto.
      * subst.
        destruct (Hmw1 eq_refl) as [_ [Hmw1a _]]. cg.
Qed.


Lemma update_AES_Closed tm SI flag n:
  AES_impl_WF SI ->
  match update_AES tm (fst (mset' SI)) SI flag n with
  | (SI',flag',_) =>
    AES_impl_WF SI' /\
    (flag'=true ->
      (AES_isClosed tm (AES_impl_to_AES SI) /\ SI=SI'))
  end.
Proof.
  intros.
  destruct (update_AES tm (fst (mset' SI)) SI flag n) as [[SI' flag'] n0_] eqn:E.
  epose proof (update_AES_spec _ _ _ _ _ H) as H0.
  rewrite E in H0.
  destruct H0 as [H0 H1].
  repeat split. 1: assumption.
  - intro; subst.
    specialize (H1 eq_refl).
    destruct H1 as [H1 [H2 H3]]; subst.
    apply AES_isClosed'_correct.
    unfold AES_isClosed'.
    destruct SI'.
    unfold AES_impl_to_AES.
    intros.
    apply H2; auto 1.
    cbn. cbn in H.
    destruct H as [_ [_ H]].
    unfold mset_WF,set_WF in H.
    rewrite H in H1.
    apply H1.
  - apply H1,H2.
Qed.


Hypothesis Σ0:Σ.
Lemma tape_seg__repeat_Σ0 x d len:
  repeat Σ0 len = tape_seg (fun _ : Z => Σ0) x d len.
Proof.
  gd x. gd d.
  induction len; cbn; intros; cg.
Qed.

Lemma InitES_InAES_cond (S:AbstractES):
  let (ls,rs,ms):=S in
  ls (repeat Σ0 len_l) ->
  rs (repeat Σ0 len_r) ->
  ms {| l:=repeat Σ0 len_l; r:=repeat Σ0 len_r; m:=Σ0; s:=St0 |} ->
  InAES (InitES Σ Σ0) S.
Proof.
  destruct S as [ls rs ms].
  intros.
  cbn.
  repeat split.
  - eexists.
    split.
    1: apply H1.
    cbn.
    repeat split; cg; apply tape_seg__repeat_Σ0.
  - unfold xset_matches. intros.
    eexists.
    split.
    1: apply H.
    apply tape_seg__repeat_Σ0.
  - unfold xset_matches. intros.
    eexists.
    split.
    1: apply H0.
    apply tape_seg__repeat_Σ0.
Qed.


Definition check_InitES_InAES (S:AES_impl):bool:=
  let (ls,rs,ms):=S in
  (snd (mset_ins0 ms {| l:=repeat Σ0 len_l; r:=repeat Σ0 len_r; m:=Σ0; s:=St0 |}) &&
  snd (xset_ins ls (repeat Σ0 len_l)) &&
  snd (xset_ins rs (repeat Σ0 len_r))) %bool.

Lemma check_InitES_InAES_spec S:
  AES_impl_WF S ->
  check_InitES_InAES S = true ->
  InAES (InitES Σ Σ0) (AES_impl_to_AES S).
Proof.
  destruct S as [ls rs ms].
  intros H0 H.
  cbn in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [[Ha Hb] Hc].
  destruct H0 as [H0a [H0b H0c]].
  unfold AES_impl_to_AES.
  eapply (InitES_InAES_cond {| lset := xset_in ls; rset := xset_in rs; mset := mset_in ms |}).
  - destruct (xset_ins ls (repeat Σ0 len_l)) as [ls' flag] eqn:E.
    cbn in E.
    destruct len_l.
    1: cbn in E,Hb; invst E; cg.
    destruct (xset_ins_spec _ _ _ _ _ H0a E) as [_ H0].
    cbn in Hb. invst Hb.
    apply H0,eq_refl.
  - destruct (xset_ins rs (repeat Σ0 len_r)) as [rs' flag] eqn:E.
    destruct len_r.
    1: cbn in E,Hc; invst E; cg.
    cbn in E.
    destruct (xset_ins_spec _ _ _ _ _ H0b E) as [_ H0].
    cbn in Hc. invst Hc.
    apply H0,eq_refl.
  - destruct (mset_ins0 ms {| l := repeat Σ0 len_l; r := repeat Σ0 len_r; m := Σ0; s := St0 |}) as [ms' flag] eqn:E.
    destruct len_l.
    1: cbn in E,Hb; invst E; cg.
    destruct len_r.
    1: cbn in E,Hc; invst E; cg.
    destruct (mset_ins0_spec _ _ _ _ H0c E) as [_ H0].
    cbn in Ha. invst Ha.
    apply H0,eq_refl.
Qed.

Fixpoint NGramCPS_decider_0(m n:nat)(tm:TM Σ)(S:AES_impl):bool :=
match m with
| O => false
| S m0 =>
  match update_AES tm (fst (mset' S)) S true n with
  | (S',flag,n0) =>
      if flag then check_InitES_InAES S'
      else NGramCPS_decider_0 m0 n0 tm S'
  end
end.

Definition NGramCPS_decider(m:nat)(tm:TM Σ):bool :=
  match len_l,len_r with
  | S _,S _ =>
    NGramCPS_decider_0 m m tm
    {|
      lset':=fst (xset_ins (PositiveMap.empty _) (repeat Σ0 len_l));
      rset':=fst (xset_ins (PositiveMap.empty _) (repeat Σ0 len_r));
      mset':=fst (mset_ins0 (nil,PositiveMap.empty _) {| l:=repeat Σ0 len_l; r:=repeat Σ0 len_r; m:=Σ0; s:=St0 |});
    |}
  | _,_ => false
  end.


Lemma NGramCPS_decider_0_spec m n tm S:
  AES_impl_WF S ->
  NGramCPS_decider_0 m n tm S = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  gd S. gd n.
  induction m; intros.
  1: cbn in H0; cg.
  cbn in H0.
  destruct (update_AES tm (fst (mset' S)) S true n) as [[S' flag] n0_] eqn:E.
  epose proof (update_AES_Closed _ _ _ _ H) as H1.
  rewrite E in H1.
  destruct H1 as [H1a H1b].
  pose proof (check_InitES_InAES_spec S' H1a).
  destruct flag.
  - specialize (H1b eq_refl).
    destruct H1b as [H1b H1c].
    specialize (H1 H0).
    subst.
    apply (AES_Closed_NonHalt _ _ _ H1 H1b).
  - eapply IHm.
    + apply H1a.
    + apply H0.
Qed.


Lemma xset_WF_empty: (xset_WF (PositiveMap.empty (list Σ * PositiveMap.tree unit))).
Proof.
  unfold xset_WF.
  intros.
  unfold xset_in.
  destruct x1; cbn; rewrite PositiveMap.gempty.
  2: rewrite pop_back'__push_back.
  2: rewrite PositiveMap.gempty.
  1,2: tauto.
Qed.


Lemma NGramCPS_decider_spec m tm:
  NGramCPS_decider m tm = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  unfold NGramCPS_decider.
  destruct len_l as [|nl];
  destruct len_r as [|nr];
  cg.
  apply NGramCPS_decider_0_spec.
  split.
  {
    destruct ((xset_ins (PositiveMap.empty (list Σ * PositiveMap.tree unit)) (repeat Σ0 (S nl)))) as [ls' flag] eqn:E.
    apply (xset_ins_spec _ _ _ _ _ xset_WF_empty E).
  }
  split.
  {
    destruct ((xset_ins (PositiveMap.empty (list Σ * PositiveMap.tree unit)) (repeat Σ0 (S nr)))) as [rs' flag] eqn:E.
    apply (xset_ins_spec _ _ _ _ _ xset_WF_empty E).
  }
  {
    destruct ((mset_ins0 (nil, PositiveMap.empty unit)
          {| l := repeat Σ0 (S nl); r := repeat Σ0 (S nr); m := Σ0; s := St0 |})) as [ms' flag] eqn:E.
    apply (mset_ins0_spec _ _ _ _ (empty_set_WF _) E).
  }
Qed.


End NGramCPS.



Section TMwithExtraInfo.

Hypothesis Σ:Set.
Hypothesis Σ':Set.
Hypothesis Σ0':Σ'.
Hypothesis F:Σ'->Σ.

Hypothesis tm:TM Σ.
Hypothesis tm':TM Σ'.
Hypothesis HF:
  forall (s:St)(i:Σ'),
  match tm' s i with
  | Some tr =>
    let (s',d,o) := tr in 
    tm s (F i) = Some {| nxt:=s'; dir:=d; out:= F o |}
  | None => tm s (F i) = None
  end.

Definition F_ES: (ExecState Σ')->(ExecState Σ) :=
  fun st =>
  let (s,t):=st in
  (s,fun x => F (t x)).

Lemma F_step st0 st1:
  step Σ tm (F_ES st0) = Some st1->
  exists st1',
  step Σ' tm' st0 = Some st1' /\
  F_ES st1' = st1.
Proof.
  destruct st0 as [s t].
  cbn.
  intro H.
  pose proof (HF s (t 0%Z)) as H0.
  destruct (tm s (F (t 0%Z))) as [[s1 d1 o1]|] eqn:E. 2: cg.
  destruct (tm' s (t 0%Z)) as [[s1' d1' o1']|] eqn:E'. 2: cg.
  invst H0; clear H0.
  eexists.
  split.
  1: reflexivity.
  cbn.
  invst H.
  f_equal.
  unfold mov,upd.
  fext.
  destruct ((x + Dir_to_Z d1' =? 0)%Z); reflexivity.
Qed.

Lemma F_step_halt st0:
  step Σ tm (F_ES st0) = None->
  step Σ' tm' st0 = None.
Proof.
  unfold step.
  destruct st0 as [s t]. cbn.
  specialize (HF s (t Z0)).
  destruct (tm' s (t 0%Z)); cbn; cg.
  destruct t0. rewrite HF. cg.
Qed.


Lemma F_Steps n st0 st1:
  Steps Σ tm n (F_ES st0) st1->
  exists st1',
  Steps Σ' tm' n st0 st1' /\
  F_ES st1' = st1.
Proof.
gd st1.
induction n; intros st1 H.
- invst H.
  exists st0.
  split. 2:reflexivity.
  ctor.
- invst H.
  destruct (IHn _ H1) as [st1' [H4 H5]].
  subst.
  destruct (F_step _ _ H3) as [st2 [H5 H6]].
  exists st2.
  split. 2: assumption.
  ector; eauto.
Qed.

Lemma F_InitES:
  InitES Σ (F Σ0') = 
  F_ES (InitES Σ' Σ0').
Proof.
  reflexivity.
Qed.

Lemma F_HaltsFromInit:
  HaltsFromInit Σ (F Σ0') tm ->
  HaltsFromInit Σ' Σ0' tm'.
Proof.
  unfold HaltsFromInit,Halts,HaltsAt.
  rewrite F_InitES.
  intro H.
  destruct H as [n [st' [H H0]]].
  exists n.
  destruct (F_Steps _ _ _ H) as [st [H1 H2]].
  exists st.
  split; auto.
  destruct st,st'.
  cbn in H2.
  invst H2.
  apply F_step_halt,H0.
Qed.

Lemma F_NonHaltsFromInit:
  ~HaltsFromInit Σ' Σ0' tm' ->
  ~HaltsFromInit Σ (F Σ0') tm.
Proof.
  pose proof F_HaltsFromInit.
  tauto.
Qed.

End TMwithExtraInfo.


Definition StΣ_neb(x1 x2:St*Σ) :=
let (s1,i1):=x1 in
let (s2,i2):=x2 in
if St_eqb s1 s2 then negb (Σ_eqb i1 i2) else true.

Definition Σ_history:Set :=
  Σ*(list (St*Σ)).

Definition Σ_history_0:Σ_history := (Σ0,nil).

Definition TM_history(n:nat)(tm:TM Σ):TM Σ_history :=
  fun s i =>
  let (i0,i1):=i in
  match tm s i0 with
  | Some tr =>
    let (s',d,o0):=tr in
    Some {|
      nxt := s';
      dir := d;
      out := (o0,firstn n ((s,i0)::i1));
    |}
  | None => None
  end.



Definition TM_history_LRU(tm:TM Σ):TM Σ_history :=
  fun s i =>
  let (i0,i1):=i in
  match tm s i0 with
  | Some tr =>
    let (s',d,o0):=tr in
    Some {|
      nxt := s';
      dir := d;
      out := (o0,((s,i0)::(filter (StΣ_neb (s,i0)) i1)));
    |}
  | None => None
  end.


Lemma TM_history_HF n tm:
  forall (s:St)(i:Σ_history),
  match TM_history n tm s i with
  | Some tr =>
    let (s',d,o) := tr in 
    tm s (fst i) = Some {| nxt:=s'; dir:=d; out:= fst o |}
  | None => tm s (fst i) = None
  end.
Proof.
  intros.
  destruct i as [i0 i1].
  cbn.
  destruct (tm s0 i0) as [[s' d o0]|]; cbn; reflexivity.
Qed.

Lemma TM_history_NonHaltsFromInit n tm:
  ~HaltsFromInit Σ_history Σ_history_0 (TM_history n tm) ->
  ~HaltsFromInit Σ (fst Σ_history_0) tm.
Proof.
  apply F_NonHaltsFromInit.
  apply TM_history_HF.
Qed.


Lemma TM_history_LRU_HF tm:
  forall (s:St)(i:Σ_history),
  match TM_history_LRU tm s i with
  | Some tr =>
    let (s',d,o) := tr in 
    tm s (fst i) = Some {| nxt:=s'; dir:=d; out:= fst o |}
  | None => tm s (fst i) = None
  end.
Proof.
  intros.
  destruct i as [i0 i1].
  cbn.
  destruct (tm s0 i0) as [[s' d o0]|]; cbn; reflexivity.
Qed.

Lemma TM_history_LRU_NonHaltsFromInit tm:
  ~HaltsFromInit Σ_history Σ_history_0 (TM_history_LRU tm) ->
  ~HaltsFromInit Σ (fst Σ_history_0) tm.
Proof.
  apply F_NonHaltsFromInit.
  apply TM_history_LRU_HF.
Qed.


Fixpoint listStΣ_enc(x:list (St*Σ)):positive:=
match x with
| nil => xH
| (St0,Σ0)::t => (listStΣ_enc t)~0~0~0~0
| (St0,Σ1)::t => (listStΣ_enc t)~1~0~0~0
| (St1,Σ0)::t => (listStΣ_enc t)~0~1~0~0
| (St1,Σ1)::t => (listStΣ_enc t)~1~1~0~0
| (St2,Σ0)::t => (listStΣ_enc t)~0~0~1~0
| (St2,Σ1)::t => (listStΣ_enc t)~1~0~1~0
| (St3,Σ0)::t => (listStΣ_enc t)~0~1~1~0
| (St3,Σ1)::t => (listStΣ_enc t)~1~1~1~0
| (St4,Σ0)::t => (listStΣ_enc t)~0~0~0~1
| (St4,Σ1)::t => (listStΣ_enc t)~1~0~0~1
end.

Lemma listStΣ_enc_inj: is_inj listStΣ_enc.
Proof.
  intros x1 x2 H.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; cbn; intros; cg.
  - destruct h2 as [s i]; destruct s,i; invst H.
  - destruct h1 as [s i]; destruct s,i; invst H.
  - destruct h1 as [s1 i1]; destruct s1,i1;
    destruct h2 as [s2 i2]; destruct s2,i2;
    invst H;
    f_equal; apply IHt1,H1.
Qed.

Definition Σ_history_enc(x:Σ_history):positive:=
  let (x0,x1):=x in
  match x0 with
  | Σ0 => (listStΣ_enc x1)~0
  | Σ1 => (listStΣ_enc x1)~1
  end.

Lemma Σ_history_enc_inj: is_inj Σ_history_enc.
Proof.
  intros x1 x2 H.
  destruct x1 as [a1 b1].
  destruct x2 as [a2 b2].
  cbn in H.
  destruct a1,a2; invst H; f_equal; apply listStΣ_enc_inj,H1.
Qed.

Definition NGramCPS_decider_impl1_0 (len_h len_l len_r m:nat) tm :=
  NGramCPS_decider Σ_history len_l len_r Σ_history_enc (listT_enc Σ_history_enc) Σ_history_0 m (TM_history len_h tm).

Definition NGramCPS_decider_impl2_0 (len_l len_r m:nat) tm :=
  NGramCPS_decider Σ len_l len_r Σ_enc (listΣ_enc) Σ0 m tm.

Definition NGramCPS_LRU_decider_0 (len_l len_r m:nat) tm :=
  NGramCPS_decider Σ_history len_l len_r Σ_history_enc (listT_enc Σ_history_enc) Σ_history_0 m (TM_history_LRU tm).

Lemma NGramCPS_decider_impl1_0_spec len_h len_l len_r m tm:
  NGramCPS_decider_impl1_0 len_h len_l len_r m tm = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  intro H.
  unfold NGramCPS_decider_impl1_0 in H.
  eapply TM_history_NonHaltsFromInit.
  eapply NGramCPS_decider_spec.
  3: apply H.
  - apply Σ_history_enc_inj.
  - apply listT_enc_inj,Σ_history_enc_inj.
Qed.

Lemma NGramCPS_decider_impl2_0_spec len_l len_r m tm:
  NGramCPS_decider_impl2_0 len_l len_r m tm = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  intro H.
  unfold NGramCPS_decider_impl2_0 in H.
  eapply NGramCPS_decider_spec; eauto 1.
  - apply Σ_enc_inj.
  - apply listΣ_inj.
Qed.

Lemma NGramCPS_LRU_decider_0_spec len_l len_r m tm:
  NGramCPS_LRU_decider_0 len_l len_r m tm = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  intro H.
  unfold NGramCPS_LRU_decider_0 in H.
  eapply TM_history_LRU_NonHaltsFromInit.
  eapply NGramCPS_decider_spec.
  3: apply H.
  - apply Σ_history_enc_inj.
  - apply listT_enc_inj,Σ_history_enc_inj.
Qed.


Definition NGramCPS_decider_impl1 (len_h len_l len_r m:nat):HaltDecider :=
  fun tm =>
  if NGramCPS_decider_impl1_0 len_h len_l len_r m tm then Result_NonHalt else Result_Unknown.

Definition NGramCPS_decider_impl2 (len_l len_r m:nat):HaltDecider :=
  fun tm =>
  if NGramCPS_decider_impl2_0 len_l len_r m tm then Result_NonHalt else Result_Unknown.

Definition NGramCPS_LRU_decider (len_l len_r m:nat):HaltDecider :=
  fun tm =>
  if NGramCPS_LRU_decider_0 len_l len_r m tm then Result_NonHalt else Result_Unknown.

Lemma NGramCPS_decider_impl1_spec len_h len_l len_r m BB:
  HaltDecider_WF BB (NGramCPS_decider_impl1 len_h len_l len_r m).
Proof.
  intros tm.
  unfold NGramCPS_decider_impl1.
  pose proof (NGramCPS_decider_impl1_0_spec len_h len_l len_r m tm).
  destruct (NGramCPS_decider_impl1_0 len_h len_l len_r m tm); tauto.
Qed.

Lemma NGramCPS_decider_impl2_spec len_l len_r m BB:
  HaltDecider_WF BB (NGramCPS_decider_impl2 len_l len_r m).
Proof.
  intros tm.
  unfold NGramCPS_decider_impl2.
  pose proof (NGramCPS_decider_impl2_0_spec len_l len_r m tm).
  destruct (NGramCPS_decider_impl2_0 len_l len_r m tm); tauto.
Qed.

Lemma NGramCPS_LRU_decider_spec len_l len_r m BB:
  HaltDecider_WF BB (NGramCPS_LRU_decider len_l len_r m).
Proof.
  intros tm.
  unfold NGramCPS_LRU_decider.
  pose proof (NGramCPS_LRU_decider_0_spec len_l len_r m tm).
  destruct (NGramCPS_LRU_decider_0 len_l len_r m tm); tauto.
Qed.




Module ListTape.

Record ListES := {
  l: list Σ;
  r: list Σ;
  m: Σ;
  s: St;
}.

Definition ListES_toES(x:ListES):ExecState Σ :=
let (l0,r0,m0,s0):=x in
(s0,
fun x =>
match x with
| Zpos x0 => nth (Pos.to_nat x0) (m0::r0) Σ0
| Zneg x0 => nth (Pos.to_nat x0) (m0::l0) Σ0
| Z0 => m0
end).

Definition ListES_step(tm:TM Σ)(x:ListES):option ListES :=
let (l0,r0,m0,s0):=x in
match tm s0 m0 with
| None => None
| Some tr =>
  let (s1,d,o) := tr in
    Some
    match d with
    | Dpos =>
      match r0 with
      | m1::r1 => {| l:=o::l0; r:=r1; m:=m1; s:=s1 |}
      | nil => {| l:=o::l0; r:=nil; m:=Σ0; s:=s1 |}
      end
    | Dneg =>
      match l0 with
      | m1::l1 => {| l:=l1; r:=o::r0; m:=m1; s:=s1 |}
      | nil => {| l:=nil; r:=o::r0; m:=Σ0; s:=s1 |}
      end
    end
end.

Lemma ListES_step_spec tm x:
  step Σ tm (ListES_toES x) =
  match ListES_step tm x with
  | None => None
  | Some x1 => Some (ListES_toES x1)
  end.
Proof.
  destruct x as [l0 r0 m0 s0].
  cbn.
  destruct (tm s0 m0) as [[s' d o]|].
  2: reflexivity.
  unfold mov,upd.
  destruct d; cbn.
  + destruct l0; cbn.
    * f_equal. f_equal. fext.
      assert (H:(x<0\/x=0\/x=1\/x>1)%Z) by lia.
      destruct H as [H|[H|[H|H]]].
      -- destruct x; try lia.
         destruct ((Z.neg p + -1)%Z) eqn:E; cbn; try lia.
         destruct (Pos.to_nat p0) eqn:E0. 1: lia.
         destruct n,(Pos.to_nat p); auto 1.
         ++ destruct n; reflexivity.
         ++ destruct n0; reflexivity.
      -- subst. reflexivity.
      -- subst. reflexivity.
      -- destruct x; try lia.
         destruct ((Z.pos p + -1)%Z) eqn:E; cbn; try lia.
         destruct (Pos.to_nat p0) eqn:E0. 1: lia.
         assert (Pos.to_nat p = S (S n)) by lia. rewrite H0. reflexivity.
    * f_equal. f_equal. fext.
      assert (H:(x<0\/x=0\/x=1\/x>1)%Z) by lia.
      destruct H as [H|[H|[H|H]]].
      -- destruct x; try lia.
         destruct ((Z.neg p + -1)%Z) eqn:E; cbn; try lia.
         destruct (Pos.to_nat p0) eqn:E0. 1: lia.
         assert (n=Pos.to_nat p) by lia. rewrite H0. reflexivity.
      -- subst. reflexivity.
      -- subst. reflexivity.
      -- destruct x; try lia.
         destruct ((Z.pos p + -1)%Z) eqn:E; cbn; try lia.
         destruct (Pos.to_nat p0) eqn:E0. 1: lia.
         assert (Pos.to_nat p = S (S n)) by lia. rewrite H0. reflexivity.
  + destruct r0; cbn.
    * f_equal. f_equal. fext.
      assert (H:(x>0\/x=0\/x=-1\/x<(-1))%Z) by lia.
      destruct H as [H|[H|[H|H]]].
      -- destruct x; try lia.
         destruct ((Z.neg p + -1)%Z) eqn:E; cbn; try lia.
         destruct (Pos.to_nat p0) eqn:E0. 1: lia.
         destruct (Pos.to_nat (p + 1)) eqn:E1; try lia.
         destruct n0,(Pos.to_nat p); auto 1.
         ++ destruct n0; reflexivity.
         ++ destruct n1; reflexivity.
      -- subst. reflexivity.
      -- subst. reflexivity.
      -- destruct x; try lia.
         destruct ((Z.neg p + 1)%Z) eqn:E; cbn; try lia.
         destruct (Pos.to_nat p0) eqn:E0. 1: lia.
         assert (Pos.to_nat p = S (S n)) by lia. rewrite H0. reflexivity.
    * f_equal. f_equal. fext.
      assert (H:(x>0\/x=0\/x=-1\/x<(-1))%Z) by lia.
      destruct H as [H|[H|[H|H]]].
      -- destruct x; try lia.
         destruct ((Z.pos p + 1)%Z) eqn:E; cbn; try lia.
         destruct (Pos.to_nat p) eqn:E0. 1: lia.
         assert (Pos.to_nat p0 = S (S n)) by lia. rewrite H0. reflexivity.
      -- subst. reflexivity.
      -- subst. reflexivity.
      -- destruct x; try lia.
         destruct ((Z.neg p + 1)%Z) eqn:E; cbn; try lia.
         destruct (Pos.to_nat p) eqn:E0. 1: lia.
         assert (n=Pos.to_nat p0) by lia. rewrite <-H0.
         destruct n. 1: lia. reflexivity.
Qed.


Definition app_halftape(h:list Σ)(t:nat->Σ):nat->Σ :=
  fun n =>
  match nth_error h n with
  | None => t (n-(length h))
  | Some c => c
  end.

Definition make_tape(l0:nat->Σ)(m0:Σ)(r0:nat->Σ):Z->Σ :=
  fun x =>
  match x with
  | Z0 => m0
  | Zpos x0 => r0 (Nat.pred (Pos.to_nat x0))
  | Zneg x0 => l0 (Nat.pred (Pos.to_nat x0))
  end.

Definition make_tape'(l1:nat->Σ)(l0:list Σ)(m0:Σ)(r0:list Σ)(r1:nat->Σ):Z->Σ :=
  make_tape (app_halftape l0 l1) m0 (app_halftape r0 r1).

Definition makeES(st:ListES)(l1 r1:nat->Σ):ExecState Σ :=
  let (l0,r0,m0,s0):=st in
  (s0, make_tape' l1 l0 m0 r0 r1).

Definition addmul(x:Z)(d:Dir)(n:nat):Z := x+(Dir_to_Z d)*(Z.of_nat n).

Definition half_tape(f:Z->Σ)(x:Z)(d:Dir):nat->Σ :=
  fun n =>
  f (addmul x d n).

Lemma make_tape'_spec (t:Z->Σ) nl nr:
  t = 
  make_tape'
    (half_tape t (-Z.of_nat(1+nl))%Z Dneg)
    (tape_seg _ t ((-1)%Z) Dneg nl)
    (t Z0)
    (tape_seg _ t (1%Z) Dpos nr)
    (half_tape t (Z.of_nat (1+nr)) Dpos).
Proof.
  fext.
  cbn.
  destruct x.
  - cbn. reflexivity.
  - cbn.
    unfold app_halftape.
    remember (Nat.pred (Pos.to_nat p)) as p0.
    destruct (tape_seg_spec Σ t 1 Dpos nr) as [H0 H1].
    assert (H:p0<nr\/nr<=p0) by lia.
    destruct H as [H|H].
    + rewrite H0; auto 1. f_equal.
      unfold Dir_to_Z. subst. lia.
    + pose proof H as H2.
      rewrite <-H1 in H.
      rewrite <-nth_error_None in H.
      rewrite H.
      unfold half_tape.
      f_equal.
      unfold addmul,Dir_to_Z.
      lia.
  - cbn.
    unfold app_halftape.
    remember (Nat.pred (Pos.to_nat p)) as p0.
    destruct (tape_seg_spec Σ t (-1) Dneg nl) as [H0 H1].
    assert (H:p0<nl\/nl<=p0) by lia.
    destruct H as [H|H].
    + rewrite H0; auto 1. f_equal.
      unfold Dir_to_Z. subst. lia.
    + pose proof H as H2.
      rewrite <-H1 in H.
      rewrite <-nth_error_None in H.
      rewrite H.
      unfold half_tape.
      f_equal.
      unfold addmul,Dir_to_Z.
      lia.
Qed.

Lemma make_tape'_lmr (t:Z->Σ):
  t = 
  make_tape'
    (half_tape t (-1) Dneg)
    nil
    (t Z0)
    nil
    (half_tape t 1 Dpos).
Proof.
  apply (make_tape'_spec t 0 0).
Qed.

Lemma make_tape'_upd l1' l1 m1 r1 r1' m1':
  upd Σ (make_tape' l1' l1 m1 r1 r1') m1' = (make_tape' l1' l1 m1' r1 r1').
Proof.
  fext.
  unfold upd.
  destruct x; cbn; reflexivity.
Qed.

Lemma app_halftape_S m1 l1 l1' n:
  app_halftape (m1 :: l1) l1' (S n) = app_halftape l1 l1' n.
Proof.
  unfold app_halftape. cbn. reflexivity.
Qed.

Lemma make_tape'_mov_l l1' l1 m1 r1 r1' σ:
  mov Σ (make_tape' l1' (σ :: l1) m1 r1 r1') Dneg = make_tape' l1' l1 σ (m1 :: r1) r1'.
Proof.
  fext.
  unfold mov,make_tape',make_tape,Dir_to_Z.
  assert (H:(x<0\/x=0\/x=1\/x>1)%Z) by lia.
  destruct H as [H|[H|[H|H]]].
  - destruct x; try lia.
    destruct (Z.neg p + -1)%Z eqn:E; try lia.
    assert (H0:(Nat.pred (Pos.to_nat p0)) = S (Nat.pred (Pos.to_nat p))) by lia.
    rewrite H0.
    apply app_halftape_S.
  - subst. reflexivity.
  - subst. reflexivity.
  - destruct x; try lia.
    destruct (Z.pos p + -1)%Z eqn:E; try lia.
    symmetry.
    assert (H0:(Nat.pred (Pos.to_nat p)) = S (Nat.pred (Pos.to_nat p0))) by lia.
    rewrite H0.
    apply app_halftape_S.
Qed.

Definition tape_rev(f:Z->Σ):Z->Σ := fun x => f (-x)%Z.

Lemma make_tape'_rev l1' l1 m1 r1 r1':
  tape_rev (make_tape' l1' l1 m1 r1 r1') = (make_tape' r1' r1 m1 l1 l1').
Proof.
  fext.
  unfold tape_rev.
  destruct x; cbn; reflexivity.
Qed.

Lemma mov_tape_rev t d:
  mov Σ (tape_rev t) d = tape_rev (mov Σ t (Dir_rev d)).
Proof.
  fext.
  unfold mov,tape_rev.
  f_equal.
  destruct d; cbn; lia.
Qed.

Lemma make_tape'_mov_r l1' l1 m1 r1 r1' σ:
  mov Σ (make_tape' l1' l1 m1 (σ :: r1) r1') Dpos = make_tape' l1' (m1 :: l1) σ r1 r1'.
Proof.
  rewrite <-make_tape'_rev.
  symmetry.
  rewrite <-make_tape'_rev.
  rewrite mov_tape_rev.
  cbn.
  rewrite make_tape'_mov_l.
  reflexivity.
Qed.

Definition half_tape_cdr(f:nat->Σ):nat->Σ :=
  fun n => f (S n).

Lemma app_halftape_cdr l1':
  app_halftape nil l1' = app_halftape (l1' 0 :: nil) (half_tape_cdr l1').
Proof.
  fext.
  destruct x; cbn.
  1: reflexivity.
  unfold app_halftape.
  destruct x; reflexivity.
Qed.

Lemma app_halftape_eq_car_cdr h t t0 h' t' t0':
  h=h' ->
  app_halftape t t0 = app_halftape t' t0' ->
  app_halftape (h::t) t0 = app_halftape (h'::t') t0'.
Proof.
  intros. subst.
  fext.
  destruct x.
  - reflexivity.
  - cbn.
    repeat rewrite app_halftape_S.
    cg.
Qed.

Lemma app_halftape_cdr' l0 l1':
  app_halftape l0 l1' = app_halftape (l0 ++ l1' 0 :: nil) (half_tape_cdr l1').
Proof.
  induction l0.
  - apply app_halftape_cdr.
  - cbn.
    apply app_halftape_eq_car_cdr; tauto.
Qed.

Lemma half_tape_cdr_cons h l1:
  (half_tape_cdr (app_halftape (h :: nil) l1)) = l1.
Proof.
  unfold half_tape_cdr,app_halftape.
  cbn.
  fext.
  destruct x; cbn; reflexivity.
Qed.


Lemma make_tape'_cdr_l l1' o r1 r1':
  make_tape' l1' nil o r1 r1' = make_tape' (half_tape_cdr l1') (l1' 0::nil) o r1 r1'.
Proof.
  unfold make_tape'.
  f_equal.
  apply app_halftape_cdr.
Qed.

Lemma make_tape'_cdr_r l1' l1 o r1':
  make_tape' l1' l1 o nil r1' = make_tape' l1' l1 o (r1' 0::nil) (half_tape_cdr r1').
Proof.
  unfold make_tape'.
  f_equal.
  apply app_halftape_cdr.
Qed.

Lemma app_halftape_nil l1:
  app_halftape nil l1 = l1.
Proof.
  unfold app_halftape.
  fext.
  destruct x; cbn; reflexivity.
Qed.

Lemma make_tape'_cons_l h l1 o r1 r2:
  (make_tape' (app_halftape (h::nil) l1) nil o r1 r2) =
  (make_tape' l1 (h::nil) o r1 r2).
Proof.
  unfold make_tape'.
  f_equal.
  cbn.
  rewrite app_halftape_nil.
  reflexivity.
Qed.

Lemma make_tape'_cons_r l2 l1 o h r1:
  (make_tape' l2 l1 o nil (app_halftape (h::nil) r1)) =
  (make_tape' l2 l1 o (h::nil) r1).
Proof.
  unfold make_tape'.
  f_equal.
  cbn.
  rewrite app_halftape_nil.
  reflexivity.
Qed.


Lemma make_tape_eq {a b c a' b' c'}:
  make_tape a b c = make_tape a' b' c' ->
  (a=a'/\b=b'/\c=c').
Proof.
  intros.
  repeat split.
  - fext.
    epose proof (fext_inv (Zneg (Pos.of_succ_nat x)) H) as H0.
    cbn in H0.
    rewrite SuccNat2Pos.pred_id in H0. apply H0.
  - epose proof (fext_inv Z0 H) as H0.
    cbn in H0. apply H0.
  - fext.
    epose proof (fext_inv (Zpos (Pos.of_succ_nat x)) H) as H0.
    cbn in H0.
    rewrite SuccNat2Pos.pred_id in H0. apply H0.
Qed.

Lemma app_halftape_eq_cons {h a b h' a' b'}:
  app_halftape (h::a) b = app_halftape (h'::a') b' ->
  (h=h'/\app_halftape a b = app_halftape a' b').
Proof.
  intro.
  split.
  1: apply (fext_inv 0 H).
  fext.
  epose proof (fext_inv (S x) H) as H0.
  repeat rewrite app_halftape_S in H0.
  apply H0.
Qed.

Lemma app_halftape_eq {a b a' b'}:
  app_halftape a b = app_halftape a' b' ->
  length a <= length a' ->
  exists ls,
  length ls = length a' - length a /\
  a++ls=a' /\
  app_halftape ls b' = b.
Proof.
  gd a'.
  induction a as [|h a]; intros.
  - exists a'. cbn.
    repeat split.
    1: lia.
    rewrite <-H. apply app_halftape_nil.
  - destruct a' as [|h' a'].
    1: cbn in H0; lia.
    destruct (app_halftape_eq_cons H) as [H1 H2].
    subst.
    cbn in H0.
    assert (H3:length a <= length a') by lia.
    specialize (IHa _ H2 H3).
    destruct IHa as [ls [H4 [H5 H6]]].
    exists ls.
    repeat split; auto 1.
    cbn. cg.
Qed.

Lemma app_halftape_eq' {a b a' b'}:
  app_halftape a b = app_halftape a' b' ->
  length a = length a' ->
  (a=a'/\b=b').
Proof.
  intros.
  eassert (H1:_) by (apply (app_halftape_eq H); lia).
  destruct H1 as [ls [H1 [H2 H3]]].
  assert (length ls = 0) by lia.
  destruct ls; cbn in H4; cg.
  rewrite app_halftape_nil in H3.
  rewrite app_nil_r in H2.
  split; cg.
Qed.


Definition AbstractSteps tm n0 (st0 st1:ListES) :=
  length st0.(l) + length st0.(r) = length st1.(l) + length st1.(r) /\
  forall l1 r1,
    Steps Σ tm n0 (makeES st0 l1 r1) (makeES st1 l1 r1).

Fixpoint getASteps(h:St*Σ*(Trans Σ))(ls:list (St*Σ*(Trans Σ))):ListES*ListES :=
  match h with
  | (s'',i'',tr'') =>
    match ls with
    | nil =>
      let x:=Build_ListES nil nil i'' s'' in
      (x,x)
    | h0::t0 =>
      let (st0,st1):=getASteps h0 t0 in
      let (l0,r0,m0,s0):=st0 in
      let (l1,r1,m1,s1):=st1 in
      match h0 with
      | (s',i',tr') =>
        let (s_,d,o):=tr' in
        match d with
        | Dpos =>
          match r1 with
          | nil =>
            (Build_ListES l0 (r0++i''::nil) m0 s0,
             Build_ListES (o::l1) nil i'' s'')
          | m2::r2 =>
            (st0, Build_ListES (o::l1) r2 m2 s'')
          end
        | Dneg =>
          match l1 with
          | nil =>
            (Build_ListES (l0++i''::nil) r0 m0 s0,
             Build_ListES nil (o::r1) i'' s'')
          | m2::l2 =>
            (st0, Build_ListES l2 (o::r1) m2 s'')
          end
        end
      end
    end
  end.

(* gen unique Asteps from (St,Σ) history *)


Inductive MoveDist: (TM Σ)->(nat)->(ExecState Σ)->(ExecState Σ)->Z->Prop :=
| MoveDist_O tm st: MoveDist tm O st st Z0
| MoveDist_S tm n st0 s1 t1 st2 d d' tr:
  MoveDist tm n st0 (s1,t1) d ->
  step Σ tm (s1,t1) = Some st2 ->
  tm s1 (t1 Z0) = Some tr ->
  (d'-d = (Dir_to_Z (dir _ tr)))%Z ->
  MoveDist tm (S n) st0 st2 d'
.

Lemma MoveDist_unique {tm n st0 st1 d st1' d'}:
  MoveDist tm n st0 st1 d ->
  MoveDist tm n st0 st1' d' ->
  (st1=st1' /\ d=d').
Proof.
  gd d'. gd st1'.
  gd d. gd st1.
  induction n.
  - intros.
    invst H. invst H0. tauto.
  - intros.
    invst H. invst H0.
    specialize (IHn _ _ _ _ H2 H5).
    destruct IHn as [IHn0 IHn1].
    invst IHn0.
    rewrite H8 in H4.
    invst H4.
    rewrite H7 in H3.
    invst H3.
    repeat split.
    rewrite <-H10 in H6.
    lia.
Qed.

Lemma getASteps_spec {tm:TM Σ} {n st0 st1 h ls}:
  Steps _ tm n st0 st1 ->
  length ls = n ->
  (forall n0, n0<=n -> exists s2 t2, Steps _ tm n0 st0 (s2,t2) /\
  match nth_error (h::ls) (n-n0) with
  | None => False
  | Some (s0,i0,tr) => tm s0 i0 = Some tr /\ s0 = s2 /\ i0 = t2 Z0
  end) ->
  let (st0',st1'):=getASteps h ls in
  AbstractSteps tm n st0' st1' /\
  (MoveDist tm n st0 st1 ((Z.of_nat (length (st1'.(l))))-(Z.of_nat (length (st0'.(l)))))) /\
  exists l1 r1,
  st0 = makeES st0' l1 r1 /\
  st1 = makeES st1' l1 r1.
Proof.
  gd st1.
  gd h. gd ls.
  induction n; intros.
  - destruct ls.
    2: cbn in H0; cg.
    specialize (H1 0).
    assert (H2:0<=0) by lia.
    specialize (H1 H2). clear H2.
    cbn in H1.
    destruct H1 as [s2 [t2 [H1a H1b]]].
    destruct h as [[s0 i0] tr].
    destruct H1b as [H1b [H1c H1d]]. subst.
    cbn.
    epose proof (Steps_unique _ H1a H). subst.
    invst H1a.
    split.
    {
      split.
      1: cg.
      intros. ctor.
    }
    split.
    1: ctor.
    eexists. eexists.
    rewrite <-make_tape'_lmr.
    tauto.
  - destruct ls as [|h0 ls]; cbn in H0.
    1: cg.
    invst H.
    invst H0.
    specialize (IHn ls h0 _ H3 eq_refl).
    cbn.
    destruct (getASteps h0 ls) as [st3 st4].
    eassert (H':_). {
      apply IHn.
      intros.
      specialize (H1 n0).
      assert (H4:S (length ls) - n0 = S ((length ls) - n0)) by lia.
      rewrite H4 in H1.
      cbn in H1.
      apply H1. lia.
    }
    clear IHn.
    destruct H' as [H'AS [H'md [l1' [r1' [H'0 H'1]]]]].
    destruct h as [[s'' i''] tr''].
    destruct h0 as [[s' i'] tr'].
    destruct st3 as [l0 r0 m0 s0].
    destruct st4 as [l1 r1 m1 s1].
    eassert (H1a:_) by (apply (H1 (length ls)); lia).
    eassert (H1b:_) by (apply (H1 (S (length ls))); lia).
    clear H1.
    destruct H1a as [s2a [t2a [H1a1 H1a2]]].
    destruct H1b as [s2b [t2b [H1b1 H1b2]]].
    epose proof (Steps_unique _ H1a1 H3) as H1.
    epose proof (Steps_unique _ H1b1 H) as H2.
    destruct st2 as [s2 t2].
    destruct st1 as [s1' t1].
    invst H1.
    invst H2.
    clear H1a1. clear H1b1.
    clear H1. clear H2.
    assert (H1:S (length ls) - length ls = 1) by lia.
    rewrite H1 in H1a2. clear H1.
    rewrite Nat.sub_diag in H1b2.
    cbn in H1a2,H1b2.
    destruct H1a2 as [H1a1 [H1a2 H1a3]].
    destruct H1b2 as [H1b1 [H1b2 H1b3]].
    subst.
    destruct tr' as [s' d o].
    destruct d.
    {
      destruct l1.
      - split.
        {
          destruct H'AS as [H'len H'AS].
          split.
          1: cbn; cbn in H'len; rewrite app_length; cbn; lia.
          intros.
          pose proof (H'AS (app_halftape (t1 Z0::nil) l1) r2) as H1.
          ector.
          - assert (E2:(makeES {| l := l0; r := r0; m := m0; s := s0 |} (app_halftape (t1 0%Z :: nil) l1) r2) = 
            (makeES {| l := l0 ++ t1 0%Z :: nil; r := r0; m := m0; s := s0 |} l1 r2)). {
              cbn. f_equal. unfold make_tape'. f_equal.
              rewrite app_halftape_cdr'.
              rewrite half_tape_cdr_cons.
              cbn.
              reflexivity.
            }
            rewrite E2 in H1.
            apply H1.
          - cbn.
            cbn in H'1.
            invst H'1.
            cbn in H1a1.
            rewrite H1a1.
            cbn in H5.
            rewrite H1a1 in H5.
            inversion H5.
            repeat rewrite H6.
            f_equal.
            f_equal.
            rewrite make_tape'_upd.
            rewrite make_tape'_cons_l.
            rewrite make_tape'_mov_l.
            reflexivity.
        }
        split.
        {
          cbn.
          cbn in H'md.
          ector; eauto 1.
          cbn.
          rewrite app_length.
          cbn. lia.
        }
        exists (half_tape_cdr l1').
        exists r1'.
        split.
        + cbn. f_equal.
          unfold make_tape'.
          f_equal.
          assert (t1 Z0 = l1' 0). {
            cbn in H'1.
            inversion H'1.
            subst.
            cbn in H5.
            cbn in H1a1.
            rewrite H1a1 in H5.
            invst H5. clear H5.
            rewrite make_tape'_upd.
            rewrite make_tape'_cdr_l.
            rewrite make_tape'_mov_l.
            reflexivity.
          }
          rewrite H1.
          apply app_halftape_cdr'.
        + cbn.
          f_equal.
          cbn in H5.
          rewrite H1a1 in H5.
          inversion H5.
          cbn in H'1.
          inversion H'1.
          rewrite make_tape'_upd.

          repeat rewrite make_tape'_cdr_l.
          rewrite make_tape'_mov_l.
          rewrite make_tape'_cdr_l.
          reflexivity.
      - split.
        {
          destruct H'AS as [H'len H'AS].
          split.
          1: cbn; cbn in H'len; lia.
          intros.
          ector; eauto 1.
          cbn.
          cbn in H'1.
          invst H'1.
          cbn in H1a1.
          rewrite H1a1.
          cbn in H5.
          rewrite H1a1 in H5.
          invst H5.
          rewrite make_tape'_upd.
          rewrite make_tape'_mov_l.
          reflexivity.
        }
        clear H'AS.
        split.
        {
          cbn.
          cbn in H'md.
          ector; eauto 1.
          cbn.
          destruct (Z.of_nat (length l0))%Z eqn:E; cbn; try lia.
          rewrite <-Pos2Z.add_pos_neg.
          lia.
        }
        clear H'md.
        exists l1'. exists r1'.
        split. 1: reflexivity.
        cbn. f_equal.
        cbn in H'1.
        inversion H'1. clear H'1.
        clear H2. clear s1.
        cbn in H5.
        rewrite H1a1 in H5.
        invst H5.
        inversion H5. clear H5.
        rewrite make_tape'_upd,make_tape'_mov_l.
        reflexivity.
    }
    {
      destruct r1.
      - split.
        {
          destruct H'AS as [H'len H'AS].
          split.
          1: cbn; cbn in H'len; rewrite app_length; cbn; lia.
          intros.
          pose proof (H'AS l2 (app_halftape (t1 Z0::nil) r1)) as H1.
          ector.
          - assert (E2:
              (makeES {| l := l0; r := r0; m := m0; s := s0 |} l2 (app_halftape (t1 0%Z :: nil) r1)) =
              (makeES {| l := l0; r := r0 ++ t1 0%Z :: nil; m := m0; s := s0 |} l2 r1)
            ). {
              cbn. f_equal. unfold make_tape'. f_equal.
              rewrite app_halftape_cdr'.
              rewrite half_tape_cdr_cons.
              cbn.
              reflexivity.
            }
            rewrite E2 in H1.
            apply H1.
          - cbn.
            cbn in H'1.
            invst H'1.
            cbn in H1a1.
            rewrite H1a1.
            cbn in H5.
            rewrite H1a1 in H5.
            inversion H5.
            repeat rewrite H6.
            f_equal.
            f_equal.
            rewrite make_tape'_upd.
            rewrite make_tape'_cons_r.
            rewrite make_tape'_mov_r.
            reflexivity.
        }
        split.
        {
          cbn.
          cbn in H'md.
          ector; eauto 1.
          cbn.
          destruct (Z.of_nat (length l0)) eqn:E; cbn; (repeat rewrite <-Pos2Z.add_pos_neg); try lia.
          destruct ((Z.of_nat (length l1) - 0) %Z) eqn:E0; cbn; (repeat rewrite <-Pos2Z.add_pos_neg); try lia.
        }
        exists l1'.
        exists (half_tape_cdr r1').
        split.
        + cbn. f_equal.
          unfold make_tape'.
          f_equal.
          assert (t1 Z0 = r1' 0). {
            cbn in H'1.
            inversion H'1.
            subst.
            cbn in H5.
            cbn in H1a1.
            rewrite H1a1 in H5.
            invst H5. clear H5.
            rewrite make_tape'_upd.
            rewrite make_tape'_cdr_r.
            rewrite make_tape'_mov_r.
            reflexivity.
          }
          rewrite H1.
          apply app_halftape_cdr'.
        + cbn.
          f_equal.
          cbn in H5.
          rewrite H1a1 in H5.
          inversion H5.
          cbn in H'1.
          inversion H'1.
          rewrite make_tape'_upd.

          repeat rewrite make_tape'_cdr_r.
          rewrite make_tape'_mov_r.
          rewrite make_tape'_cdr_r.
          reflexivity.
      - split.
        {
          destruct H'AS as [H'len H'AS].
          split.
          1: cbn; cbn in H'len; lia.
          intros.
          ector; eauto 1.
          cbn.
          cbn in H'1.
          invst H'1.
          cbn in H1a1.
          rewrite H1a1.
          cbn in H5.
          rewrite H1a1 in H5.
          invst H5.
          rewrite make_tape'_upd.
          rewrite make_tape'_mov_r.
          reflexivity.
        }
        clear H'AS.
        split.
        {
          cbn.
          cbn in H'md.
          ector; eauto 1.
          cbn.
          destruct (Z.of_nat (length l0))%Z eqn:E; cbn; try lia.
          destruct ((Z.of_nat (length l1) - 0) %Z) eqn:E0; cbn; (repeat rewrite <-Pos2Z.add_pos_neg); try lia.
          rewrite <-Pos2Z.add_pos_neg. lia.
        }
        clear H'md.
        exists l1'. exists r1'.
        split. 1: reflexivity.
        cbn. f_equal.
        cbn in H'1.
        inversion H'1. clear H'1.
        clear H2. clear s1.
        cbn in H5.
        rewrite H1a1 in H5.
        invst H5.
        inversion H5. clear H5.
        rewrite make_tape'_upd,make_tape'_mov_r.
        reflexivity.
    }
Qed.


Lemma ex_sitr_history {tm:TM Σ} {n st0 st1}:
  Steps _ tm (S n) st0 st1 ->
  exists h ls,
  length ls = n /\
  (forall n0, n0<=n -> exists s2 t2, Steps _ tm n0 st0 (s2,t2) /\
  match nth_error (h::ls) (n-n0) with
  | None => False
  | Some (s0,i0,tr) => tm s0 i0 = Some tr /\ s0 = s2 /\ i0 = t2 Z0
  end).
Proof.
  gd st1.
  induction n.
  - intros.
    invst H.
    invst H1. clear H. clear H1.
    destruct st2 as [s0 t0].
    cbn in H3.
    destruct (tm s0 (t0 Z0)) as [tr|] eqn:E. 2: cg.
    exists (s0,t0 Z0,tr).
    exists nil.
    cbn.
    split. 1: reflexivity.
    intros.
    destruct n0. 2: lia.
    exists s0. exists t0.
    split.
    1: ctor.
    repeat split.
    cg.
  - intros.
    invst H.
    specialize (IHn _ H1).
    destruct IHn as [h' [ls' [IHn1 IHn2]]].
    destruct st2 as [s0 t0].
    cbn in H3.
    destruct (tm s0 (t0 Z0)) as [tr|] eqn:E. 2: cg.
    exists (s0,t0 Z0,tr).
    exists (h'::ls').
    split.
    1: cbn; cg.
    intros.
    assert (H2:n0<=n\/n0=S n) by lia.
    destruct H2 as [H2|H2].
    + assert (H4:S n - n0 = S (n-n0)) by lia.
      rewrite H4. cbn.
      apply IHn2,H2.
    + assert (H4:S n - n0 = 0) by lia.
      rewrite H4. cbn.
      subst.
      exists s0. exists t0.
      split; tauto.
Qed.

Lemma Steps_split{tm n1 n2 st0 st1}:
  Steps Σ tm (n1+n2) st0 st1 ->
  exists st2,
  Steps Σ tm n2 st0 st2 /\
  Steps Σ tm n1 st2 st1.
Proof.
  gd st1.
  induction n1; intros.
  - exists st1.
    split. 1: apply H.
    ctor.
  - invst H.
    specialize (IHn1 _ H1).
    destruct IHn1 as [st3 [I1 I2]].
    exists st3.
    split; auto 1.
    ector; eauto 1.
Qed.

Lemma half_tape_make_tape_r {l0 m0 r0}:
  (half_tape (make_tape l0 m0 r0)) 1 Dpos = r0.
Proof.
  unfold make_tape,half_tape,addmul,Dir_to_Z.
  fext.
  destruct (1 + 1 * Z.of_nat x)%Z eqn:E; try lia.
  f_equal.
  lia.
Qed.

Lemma half_tape_make_tape_l {l0 m0 r0}:
  (half_tape (make_tape l0 m0 r0)) (-1) Dneg = l0.
Proof.
  unfold make_tape,half_tape,addmul,Dir_to_Z.
  fext.
  destruct (-1 + -1 * Z.of_nat x)%Z eqn:E; try lia.
  f_equal.
  lia.
Qed.

Definition half_tape_all0:nat->Σ :=
  (fun _=>Σ0).

Lemma app_halftape_all0{l1 l2}:
  app_halftape l1 l2 = half_tape_all0 ->
  l2 = half_tape_all0.
Proof.
  unfold half_tape_all0.
  intros.
  fext.
  epose proof (fext_inv ((length l1)+x) H) as H0.
  cbn in H0.
  unfold app_halftape in H0.
  destruct (nth_error l1 (length l1 + x)) eqn:E.
  - assert (E1:length l1 <= length l1 + x) by lia.
    rewrite <-nth_error_None in E1. cg.
  - rewrite <-H0. f_equal. lia.
Qed.

Lemma app_halftape_assoc{l1 l2 l3}:
  app_halftape l1 (app_halftape l2 l3) =
  app_halftape (l1++l2) l3.
Proof.
  induction l1.
  - cbn. rewrite app_halftape_nil. reflexivity.
  - cbn. apply app_halftape_eq_car_cdr; auto 1.
Qed.


Lemma loop1_nonhalt (tm:TM Σ) n s0 t0:
  n<>0 ->
  (forall n0, n0<=n -> exists s2 t2 s2' t2',
    Steps _ tm n0 (s0,t0) (s2,t2) /\
    Steps _ tm (n+n0) (s0,t0) (s2',t2') /\
    s2=s2' /\
    t2 Z0 = t2' Z0) ->
  (exists s2 t2 d, MoveDist tm n (s0,t0) (s2,t2) d /\
    (d=Z0 \/
    (d>0)%Z /\
    ((half_tape t0 1 Dpos)=half_tape_all0)
    \/
    (d<0)%Z /\
    ((half_tape t0 (-1) Dneg)=half_tape_all0)
  )) ->
  ~Halts _ tm (s0,t0).
Proof.
  intros.
  assert (exists st0, Steps _ tm (S(n+n)) (s0,t0) st0). {
    eassert (H2:_) by (apply (H0 n); lia).
    eassert (H3:_) by (apply (H0 1); lia).
    destruct H2 as [s20 [t20 [s2'0 [t2'0 [H21 [H22 [H23 H24]]]]]]].
    destruct H3 as [s21 [t21 [s2'1 [t2'1 [H31 [H32 [H33 H34]]]]]]].
    subst.
    rewrite Nat.add_1_r in H32.
    inversion H32.
    epose proof (Steps_unique _ H21 H3). subst.
    cbn in H5.
    rewrite H24 in H5.
    destruct (tm s2'0 (t2'0 0%Z)) as [tr|] eqn:E; cg.
    destruct tr as [s' d o].
    eexists.
    ector.
    1: apply H22.
    cbn.
    rewrite E.
    reflexivity.
  }
  destruct H2 as [st2 H2].
  assert (E1:S (n+n) = (S n)+n) by lia.
  rewrite E1 in H2.
  epose proof (Steps_split H2) as H3.
  destruct H3 as [st3 [H3 H4]].
  epose proof (ex_sitr_history H4) as H5.
  destruct H5 as [h [ls [H5a H5b]]].
  inversion H4.
  epose proof (getASteps_spec H6 H5a H5b) as X1. subst.

  rewrite Nat.add_comm in H2.
  epose proof (Steps_split H2) as H3'.
  destruct H3' as [st3' [H3' H4']].
  epose proof (ex_sitr_history H3') as H5'.
  destruct H5' as [h' [ls' [H5a' H5b']]].
  inversion H3'.
  epose proof (getASteps_spec H7 H5a' H5b') as X2. subst.

  assert (E2:(h'::ls')=(h::ls)). {
    apply list_eq__nth_error.
    1: cbn; cg.
    intros n H5. cbn in H5.
    eassert (A:_) by (apply (H5b (length ls - n)); lia).
    eassert (A':_) by (apply (H5b' (length ls' - n)); lia).
    assert (B1:(length ls - (length ls - n)) = n) by lia.
    assert (B1':(length ls - (length ls' - n)) = n) by lia.
    rewrite B1 in A. clear B1.
    rewrite B1' in A'. clear B1'.
    destruct A as [s2 [t2 [A1 A2]]].
    destruct A' as [s2' [t2' [A1' A2']]].
    destruct (nth_error (h :: ls) n). 2: contradiction.
    destruct (nth_error (h' :: ls') n). 2: contradiction.
    destruct p as [[s4 i4] tr].
    destruct p0 as [[s4' i4'] tr'].
    destruct A2 as [A2 [A3 A4]].
    destruct A2' as [A2' [A3' A4']].
    subst.
    epose proof (Steps_trans _ H3 A1) as B1.
    eassert (B2:_) by (apply (H0 (length ls - n)); lia).
    rewrite H5a' in A1'.
    destruct B2 as [s5 [i5 [s6 [i6 [B2 [B3 [B4 B5]]]]]]].
    rewrite Nat.add_comm in B3.
    epose proof (Steps_unique _ B3 B1) as B6.
    epose proof (Steps_unique _ A1' B2) as B7.
    invst B6. invst B7.
    rewrite B5.
    rewrite B5 in A2'.
    rewrite A2' in A2.
    invst A2.
    reflexivity.
  }
  invst E2. clear E2.
  destruct (getASteps h ls) as [st0' st1'].
  epose proof (Steps_unique _ H3 H7); subst.
  destruct X1 as [X1a [X1b [l1 [r1 [X1c X1d]]]]].
  destruct X2 as [X2a [X2b [l1' [r1' [X2c X2d]]]]].
  destruct st1 as [s1 t1].
  destruct st0 as [s2 t2].
  destruct st0' as [l'0 r'0 m'0 s'0].
  destruct st1' as [l'1 r'1 m'1 s'1].
  cbn in X1c,X1d,X2c,X2d.
  inversion X1c.
  inversion X1d.
  inversion X2c.
  inversion X2d.
  subst s'0. subst s'1. subst s1. subst s2.
  clear X1c. clear X1d.
  clear X2c. clear X2d.
  cbn in X1b,X2b.
  assert (m'0=m'1). {
    rewrite H17 in H11.
    pose proof (fext_inv Z0 H11).
    cbn in H5. cg.
  }
  subst m'1.
  destruct X2a as [X3 X4].
  cbn in X3.

  destruct H1 as [s7 [t7 [d [H1a H1b]]]].
  epose proof (MoveDist_unique H1a X2b) as C1.
  destruct C1 as [C1 C2].
  inversion C1. subst s7. subst t7. clear C1.

  rewrite H11 in H17.
  destruct (make_tape_eq H17) as [D1 [D2 D3]].


  destruct H1b as [H1b|[H1b|H1b]].
  {
    subst d.
    assert (E2:length l'1 = length l'0) by lia.
    assert (E3:length r'1 = length r'0) by lia.
    symmetry in E2,E3.
    destruct (app_halftape_eq' D1 E2) as [D1a D1b].
    destruct (app_halftape_eq' D3 E3) as [D2a D2b].
    subst.
    intro F1.
    destruct F1 as [n F1].
    remember (s0, make_tape' l1' l'1 m'0 r'1 r1') as st.
    remember (length ls) as n0.
    assert (G1:forall n2, Steps _ tm (n2*n0) st st). {
      intros.
      induction n2.
      - cbn. ctor.
      - cbn. eapply Steps_trans; eauto 1.
    }
    specialize (G1 (S n)).
    destruct n0 as [|n0]. 1: lia.
    eapply (Steps_NonHalt); eauto 1. lia.
  }
  {
    destruct H1b as [H1b H1c].
    subst d.
    assert (E2:length l'0 <= length l'1) by lia.
    assert (E3:length r'1 <= length r'0) by lia.
    destruct (app_halftape_eq D1 E2) as [l3 [D1a [D1b D1c]]].
    symmetry in D3.
    destruct (app_halftape_eq D3 E3) as [r3 [D2a [D2b D2c]]].
    subst.
    clear D1. clear D2. clear D3.
    unfold make_tape' in H1c.
    rewrite half_tape_make_tape_r in H1c.


    unfold makeES in X4.
    remember (length ls) as n0.
    assert (G1:forall n2, exists l5, Steps _ tm (n2*n0)
    (s0, make_tape' l1' l'0 m'0 (r'1 ++ r3) (app_halftape r3 r1))
    (s0, make_tape' l1' (l'0++l5) m'0 (r'1 ++ r3) (app_halftape r3 r1))
    ). {
      intros.
      induction n2.
      1: exists nil; cbn; rewrite app_nil_r; ctor.
      destruct IHn2 as [l5 IHn2].
      exists (l3++l5).
      cbn.
      eapply Steps_trans; eauto 1.
      epose proof (X4 (app_halftape l5 l1') (app_halftape r3 r1)) as G2.
      unfold make_tape' in G2.
      unfold make_tape'.

      repeat rewrite app_halftape_assoc in G2.
      repeat rewrite <-app_assoc in G2.
      repeat rewrite app_halftape_assoc.
      repeat rewrite <-app_assoc.

      pose proof (app_halftape_all0 H1c) as E4.
      pose proof (app_halftape_all0 E4) as E5.

      pose proof H1c as H1d.
      rewrite E4,<-E5 in H1d.
      repeat rewrite app_halftape_assoc in H1c.
      repeat rewrite <-app_assoc in H1c.
      rewrite H1c.
      rewrite H1c in G2.
      rewrite H1d,E5 in G2.
      apply G2.
    }
    intro F1.
    destruct F1 as [n F1].
    specialize (G1 (S n)).
    destruct G1 as [l5 G1].
    destruct n0 as [|n0]. 1: lia.
    eapply (Steps_NonHalt); eauto 1. lia.
  }
  {
    destruct H1b as [H1b H1c].
    subst d.
    assert (E2:length l'1 <= length l'0) by lia.
    assert (E3:length r'0 <= length r'1) by lia.
    symmetry in D1.
    destruct (app_halftape_eq D1 E2) as [l3 [D1a [D1b D1c]]].
    destruct (app_halftape_eq D3 E3) as [r3 [D2a [D2b D2c]]].
    subst.
    clear D1. clear D2. clear D3.
    unfold make_tape' in H1c.
    rewrite half_tape_make_tape_l in H1c.


    unfold makeES in X4.
    remember (length ls) as n0.
    assert (G1:forall n2, exists r5, Steps _ tm (n2*n0)
      (s0, make_tape' (app_halftape l3 l1) (l'1 ++ l3) m'0 r'0 r1')
      (s0, make_tape' (app_halftape l3 l1) (l'1 ++ l3) m'0 (r'0++r5) r1')
    ). {
      intros.
      induction n2.
      1: exists nil; cbn; rewrite app_nil_r; ctor.
      destruct IHn2 as [r5 IHn2].
      exists (r3++r5).
      cbn.
      eapply Steps_trans; eauto 1.
      epose proof (X4 (app_halftape l3 l1) (app_halftape r5 r1')) as G2.
      unfold make_tape' in G2.
      unfold make_tape'.

      repeat rewrite app_halftape_assoc in G2.
      repeat rewrite <-app_assoc in G2.
      repeat rewrite app_halftape_assoc.
      repeat rewrite <-app_assoc.

      pose proof (app_halftape_all0 H1c) as E4.
      pose proof (app_halftape_all0 E4) as E5.

      pose proof H1c as H1d.
      rewrite E4,<-E5 in H1d.
      repeat rewrite app_halftape_assoc in H1c.
      repeat rewrite <-app_assoc in H1c.
      rewrite H1c.
      rewrite H1c in G2.
      rewrite H1d,E5 in G2.
      apply G2.
    }
    intro F1.
    destruct F1 as [n F1].
    specialize (G1 (S n)).
    destruct G1 as [l5 G1].
    destruct n0 as [|n0]. 1: lia.
    eapply (Steps_NonHalt); eauto 1. lia.
  }
Qed.


Definition ListES_step'(tr:Trans Σ)(x:ListES):ListES :=
let (l0,r0,m0,s0):=x in
  let (s1,d,o) := tr in
    match d with
    | Dpos =>
      match r0 with
      | m1::r1 => {| l:=o::l0; r:=r1; m:=m1; s:=s1 |}
      | nil => {| l:=o::l0; r:=nil; m:=Σ0; s:=s1 |}
      end
    | Dneg =>
      match l0 with
      | m1::l1 => {| l:=l1; r:=o::r0; m:=m1; s:=s1 |}
      | nil => {| l:=nil; r:=o::r0; m:=Σ0; s:=s1 |}
      end
    end.

Lemma ListES_step'_spec tm l0 r0 m0 s0:
  step Σ tm (ListES_toES (Build_ListES l0 r0 m0 s0)) =
  match tm s0 m0 with
  | Some tr => Some (ListES_toES (ListES_step' tr (Build_ListES l0 r0 m0 s0)))
  | None => None
  end.
Proof.
  erewrite (ListES_step_spec).
  cbn.
  destruct (tm s0 m0) as [[s1 d o]|]; reflexivity.
Qed.

Fixpoint verify_loop1(h0 h1:ListES*Z)(ls0 ls1:list (ListES*Z))(n:nat)(dpos:Z):bool :=
  let (es0,d0):=h0 in
  let (es1,d1):=h1 in
  St_eqb es0.(s) es1.(s) &&&
  Σ_eqb es0.(m) es1.(m) &&&
  (
    match n with
    | O =>
      match dpos with
      | Z0 => Z.eqb d1 d0
      | Zpos _ =>
        match es1.(r) with
        | nil => Z.ltb d1 d0
        | _ => false
        end
      | Zneg _ =>
        match es1.(l) with
        | nil => Z.ltb d0 d1
        | _ => false
        end
      end
    | _ => false
    end |||
    match ls0,ls1 with
    | h0'::ls0',h1'::ls1' =>
      verify_loop1 h0' h1' ls0' ls1' (Nat.pred n) dpos
    | _,_ => false
    end
  ).



Fixpoint find_loop1(h0 h1 h2:ListES*Z)(ls0 ls1 ls2:list (ListES*Z))(n:nat){struct ls1}:bool :=
(
  (let (es0,d0):=h0 in
  let (es1,d1):=h1 in
  St_eqb es0.(s) es1.(s) &&&
  let (es2,d2):=h2 in
  St_eqb es0.(s) es2.(s) &&&

  Σ_eqb es0.(m) es1.(m) &&&
  Σ_eqb es0.(m) es2.(m) &&&

  (verify_loop1 h0 h1 ls0 ls1 (S n) (d0-d1)))
)|||
  match ls2,ls1 with
  | h3::h2'::ls2',h1'::ls1' =>
    find_loop1 h0 h1' h2' ls0 ls1' ls2' (S n)
  | _,_ => false
  end.

Definition find_loop1_0(h0 h1:ListES*Z)(ls:list (ListES*Z)):bool :=
match ls with
| h2::ls' => find_loop1 h0 h1 h2 (h1::ls) ls ls' O
| nil => false
end.

Definition sidpos_history_WF tm (h:ListES*Z)(ls:list (ListES*Z)):=
  forall n, n<=(length ls) ->
  match nth_error (h::ls) ((length ls)-n) with
  | Some (es,d) => MoveDist tm n (InitES Σ Σ0) (ListES_toES es) d
  | None => False
  end.

Definition sidpos_history_period (h:ListES*Z)(ls:list (ListES*Z))(n1 T:nat):=
  forall n, n<n1 ->
  match nth_error (h::ls) n,nth_error (h::ls) (T+n) with
  | Some (es1,d1),Some (es2,d2) => es1.(s) = es2.(s) /\ es1.(m) = es2.(m)
  | _,_ => False
  end.

Lemma sidpos_history_WF_cdr tm h h1 ls:
  sidpos_history_WF tm h (h1::ls) ->
  sidpos_history_WF tm h1 ls.
Proof.
  unfold sidpos_history_WF.
  intros.
  specialize (H n).
  replace (length (h1 :: ls) - n) with (S (length ls - n)) in H.
  apply H.
  cbn. lia.
  cbn. destruct n; lia.
Qed.

Lemma skipn_S {T} {n} {h:T} {t ls}:
  h::t = skipn n ls ->
  t = skipn (S n) ls.
Proof.
  gd ls. gd t. gd h.
  induction n; intros.
  - cbn. cbn in H.
    subst. reflexivity.
  - destruct ls as [|h0 t0].
    1: cbn in H; cg.
    cbn in H. cbn.
    apply (IHn _ _ _ H).
Qed.

Lemma skipn_S' {T} {n} {h h':T} {t t'}:
  h::t = skipn n (h'::t') ->
  t = skipn n t'.
Proof.
gd t. gd t'. gd h. gd h'.
induction n; intros.
- cbn. invst H. reflexivity.
- destruct t' as [|h'' t''].
  1: cbn in H; rewrite skipn_nil in H; invst H.
  cbn. cbn in H.
  eapply IHn; eauto 1.
Qed.

Lemma nth_error_skipn {T} {h:T} {ls0 ls1 n}:
  h :: ls1 = skipn n ls0 ->
  nth_error ls0 n = Some h.
Proof.
  gd ls1. gd ls0. gd h.
  induction n; intros.
  - cbn. cbn in H.
    rewrite <-H. reflexivity.
  - cbn. destruct ls0 as [|h1 ls0].
    1: invst H.
    cbn in H.
    eapply IHn; eauto 1.
Qed.

Lemma skipn_S_n {T} n (ls:list T):
  skipn (S n) ls = tl (skipn n ls).
Proof.
  gd ls.
  induction n; intros.
  1: reflexivity.
  cbn.
  destruct ls.
  1: reflexivity.
  destruct ls.
  1: rewrite skipn_nil; reflexivity.
  specialize (IHn (t0::ls)).
  rewrite <-IHn.
  reflexivity.
Qed.

Lemma skipn_skipn {T} n1 n2 (ls:list T):
  skipn n1 (skipn n2 ls) = skipn (n1+n2) ls.
Proof.
  gd ls. gd n2.
  induction n1; intros.
  1: reflexivity.
  epose proof (IHn1 n2 ls).
  assert (E:S n1 + n2 = S (n1+n2)) by lia.
  rewrite E.
  repeat rewrite skipn_S_n.
  f_equal. apply IHn1.
Qed.



Lemma sidpos_history_period_S {h0 ls0 ls1 ls2 l0 l1 z z0 N T}:
  (l0, z) :: ls1 = skipn N (h0 :: ls0) ->
  (l1, z0) :: ls2 = skipn (S T) ((l0, z) :: ls1) ->
  sidpos_history_period h0 ls0 N (S T) ->
  s l0 = s l1 ->
  m l0 = m l1 ->
  sidpos_history_period h0 ls0 (S N) (S T).
Proof.
  unfold sidpos_history_period. cbn.
  intros.
  assert (E1:n<N\/n=N) by lia.
  destruct E1 as [E1|E1].
  1: apply H1,E1.
  subst.
  erewrite nth_error_skipn; eauto 1. cbn.
  assert (H5:(l1, z0) :: ls2 = skipn (S T) ((l0,z)::ls1)) by apply H0. clear H0.
  rewrite H in H5.
  rewrite skipn_skipn in H5. cbn in H5.
  erewrite nth_error_skipn; eauto 1. cbn.
  split; auto 1.
Qed.

Lemma sidpos_history_period_S' {h0 h0' ls0' N T}:
  sidpos_history_period h0 (h0' :: ls0') (S N) (S T) ->
  sidpos_history_period h0' ls0' N (S T).
Proof.
  unfold sidpos_history_period.
  intros.
  specialize (H (S n)).
  replace (S T + S n) with (S (S T + n)) in H by lia.
  cbn in H. cbn.
  apply H. lia.
Qed.

Lemma Steps_NonHalt_trans {tm n st st0}:
  Steps Σ tm n st st0 ->
  ~Halts Σ tm st0 ->
  ~Halts Σ tm st.
Proof.
  repeat rewrite <-NonHalt_iff.
  unfold NonHalt.
  intros.
  assert (E:n0<n\/n<=n0) by lia.
  destruct E as [E|E].
  - assert (E0:n=(n-n0+n0)) by lia.
    rewrite E0 in H.
    epose proof (Steps_split H) as H1.
    destruct H1 as [st2 [H1a H1b]].
    exists st2. apply H1a.
  - specialize (H0 (n0-n)).
    destruct H0 as [st' H0].
    exists st'.
    assert (E1:n0=n0-n+n) by lia.
    rewrite E1.
    eapply Steps_trans; eauto 1.
Qed.

Lemma MoveDist_Steps {tm n st st0 d}:
  MoveDist tm n st st0 d ->
  Steps Σ tm n st st0.
Proof.
  intros.
  induction H.
  1: ctor.
  ector; eauto 1.
Qed.


Lemma MoveDist_split {tm n1 n2 st st0 d}:
  MoveDist tm (n1+n2) st st0 d ->
  exists st1 d1,
  MoveDist tm n2 st st1 d1 /\
  MoveDist tm n1 st1 st0 (d-d1).
Proof.
gd d. gd st0.
induction n1; intros.
- cbn in H.
  exists st0. exists d.
  split; auto 1.
  replace (d-d)%Z with 0%Z by lia.
  ctor.
- cbn in H.
  invst H.
  specialize (IHn1 _ _ H1).
  destruct IHn1 as [st1 [d1 [IHn1a IHn1b]]].
  exists st1. exists d1.
  split; auto 1.
  ector; eauto 1.
  rewrite <-H5. lia.
Qed.

Lemma MoveDist_minus {tm n1 n2 st st0 st1 d d1}:
  MoveDist tm (n1+n2) st st0 d ->
  MoveDist tm n2 st st1 d1 ->
  MoveDist tm n1 st1 st0 (d-d1).
Proof.
  intros.
  destruct (MoveDist_split H) as [st3 [d3 [H1 H2]]].
  destruct (MoveDist_unique H1 H0). cg.
Qed.

Lemma loop1_nonhalt' tm l0 l1 z z0 h0 ls0 ls1 ls2 T d:
  sidpos_history_WF tm h0 ls0 ->
  sidpos_history_period h0 ls0 (S (S T)) (S T) ->
  (l0, z) :: ls1 = skipn (S T) (h0 :: ls0) ->
  (l1, z0) :: ls2 = skipn (S T) ((l0, z) :: ls1) ->
  match d with
  | 0%Z => (z0 =? z)%Z
  | Z.pos _ => match r l1 with
               | nil => (z0 <? z)%Z
               | _ :: _ => false
               end
  | Z.neg _ => match l l1 with
               | nil => (z <? z0)%Z
               | _ :: _ => false
               end
  end = true ->
  ~ HaltsFromInit Σ Σ0 tm.
Proof.
  unfold sidpos_history_WF,sidpos_history_period.
  intros.
  assert (A1:(S T)+(S T)<=length ls0). {
    assert (H0a:S T < S (S T)) by lia.
    specialize (H0 (S T) H0a). clear H0a.
    rewrite (nth_error_skipn H1) in H0.
    rewrite H1 in H2.
    rewrite skipn_skipn in H2.
    assert (H4:nth_error (h0 :: ls0) ((S T)+(S T)) <> None) by (epose proof (nth_error_skipn H2); cg).
    rewrite nth_error_Some in H4. cbn in H4.
    lia.
  }
  assert (A2:(S T)<=length ls0) by lia.
  eassert (B1:_) by (apply (H (length ls0 - (S T+S T))); lia).
  eassert (B2:_) by (apply (H (length ls0 - (S T))); lia).
  replace (length ls0 - (length ls0 - (S T + S T))) with ((S T + S T)) in B1 by lia.
  replace (length ls0 - (length ls0 - (S T))) with ((S T)) in B2 by lia.

  destruct (nth_error (h0 :: ls0) ((S T + S T))) eqn:E1. 2: contradiction.
  destruct p as [es1 d1].
  destruct (nth_error (h0 :: ls0) ((S T))) eqn:E2. 2: contradiction.
  destruct p as [es2 d2].

  epose proof (MoveDist_Steps B1) as B1'.
  apply (Steps_NonHalt_trans B1').
  destruct (ListES_toES es1) as [s1 t1] eqn:Ees1.
  destruct (ListES_toES es2) as [s2 t2] eqn:Ees2.
  apply loop1_nonhalt with (n:=S T).
  1: lia.
  {
    clear H3.
    intros.
    eassert (D1:_) by (apply (H (length ls0 - (S T+S T)+n0)); lia).
    eassert (D2:_) by (apply (H (length ls0 - (S T)+n0)); lia).

    replace ((length ls0 - (length ls0 - (S T + S T) + n0))) with (S T + (S T - n0)) in D1 by lia.
    replace ((length ls0 - (length ls0 - (S T) + n0))) with (S T - n0) in D2 by lia.

    eassert (D3:_) by (apply (H0 ((S T)-n0)); lia).
    destruct (nth_error (h0 :: ls0) (S T + (S T - n0))). 2: contradiction.
    destruct (nth_error (h0 :: ls0) ((S T - n0))). 2: contradiction.
    destruct p as [es3 d3].
    destruct p0 as [es4 d4].
    destruct D3 as [D3a D3b].

    replace ((length ls0 - (S T + S T) + n0)) with (n0 + (length ls0 - (S T + S T))) in D1 by lia.
    epose proof (MoveDist_minus D1 B1) as G1.
    replace ((length ls0 - (S T) + n0)) with ((S T + n0) + (length ls0 - (S T + S T))) in D2 by lia.
    epose proof (MoveDist_minus D2 B1) as G2.
    epose proof (MoveDist_Steps G1) as G1'.
    epose proof (MoveDist_Steps G2) as G2'.
    destruct (ListES_toES es3) as [s5 t5] eqn:E3.
    destruct (ListES_toES es4) as [s6 t6] eqn:E4.

    exists s5. exists t5.
    exists s6. exists t6.
    repeat split; auto 1.
    - destruct es3,es4.
      cbn in D3a,D3b,E3,E4.
      invst E3. invst E4.
      reflexivity.
    - destruct es3,es4.
      cbn in D3a,D3b,E3,E4.
      invst E3. invst E4.
      reflexivity.
  }
  {
    exists s2. exists t2. exists (d2-d1)%Z.
    split.
    1: eapply MoveDist_minus; eauto 1;
       replace (S T + (length ls0 - (S T + S T))) with (length ls0 - S T) by lia; assumption.

    epose proof (nth_error_skipn H1) as C1.
    rewrite H1 in H2.
    rewrite skipn_skipn in H2.
    epose proof (nth_error_skipn H2) as C2.
    rewrite E1 in C2.
    rewrite E2 in C1.
    invst C1. invst C2. clrs.
    destruct d.
    - left. lia.
    - right. left.
      destruct l1 as [l' r' m' s'].
      destruct r' eqn:E3; cbn in H3; cg.
      split. 1: lia.
      cbn in Ees1. invst Ees1.
      unfold half_tape,half_tape_all0,addmul,Dir_to_Z; fext.
      destruct (1 + 1 * Z.of_nat x)%Z eqn:E3; try lia.
      destruct (Pos.to_nat p0) eqn:E4; try lia.
      destruct n; reflexivity.
    - right. right.
      destruct l1 as [l' r' m' s'].
      destruct l' eqn:E3; cbn in H3; cg.
      split. 1: lia.
      cbn in Ees1. invst Ees1.
      unfold half_tape,half_tape_all0,addmul,Dir_to_Z; fext.
      destruct (-1 + -1 * Z.of_nat x)%Z eqn:E3; try lia.
      destruct (Pos.to_nat p0) eqn:E4; try lia.
      destruct n; reflexivity.
  }
Qed.

Ltac Σ_eq_dec s1 s2 :=
  eq_dec Σ_eqb_spec Σ_eqb s1 s2.

Lemma verify_loop1_spec tm h1 h2 ls1 ls2 n d:
  (exists h0 ls0 n0 n1,
  sidpos_history_WF tm h0 ls0 /\
  (h1::ls1) = skipn n0 (h0::ls0) /\
  (h2::ls2) = skipn (S n1) (h1::ls1) /\
  sidpos_history_period h0 ls0 n0 (S n1) /\
  n0+n=(S n1)) ->
  verify_loop1 h1 h2 ls1 ls2 n d = true ->
  ~ HaltsFromInit Σ Σ0 tm.
Proof.
  gd ls2. gd h2. gd h1. gd n.
  induction ls1; intros.
  - cbn in H0.
    destruct h1,h2.
    repeat rewrite andb_shortcut_spec in H0.
    repeat rewrite Bool.andb_true_iff in H0.
    repeat rewrite orb_shortcut_spec in H0.
    repeat rewrite Bool.orb_true_iff in H0.
    destruct H0 as [H0a [H0b [H0c _]]].
    destruct H as [h0 [ls0 [N [T [Ha [Hb [Hc [Hd He]]]]]]]].
    destruct n; cg.
    cbn in Hc. rewrite skipn_nil in Hc. invst Hc.
  - cbn in H0.
    destruct h1,h2.
    repeat rewrite andb_shortcut_spec in H0.
    repeat rewrite Bool.andb_true_iff in H0.
    repeat rewrite orb_shortcut_spec in H0.
    repeat rewrite Bool.orb_true_iff in H0.
    destruct H0 as [H0a [H0b H0c]].

    destruct H as [h0 [ls0 [N [T [Ha [Hb [Hc [Hd He]]]]]]]].
    St_eq_dec (s l0) (s l1); cg.
    Σ_eq_dec (m l0) (m l1); cg.
    clrs.

    destruct ls2 as [|h2' ls2']; cg.
    + destruct H0c as [H0c|H0c]; cg.
      destruct n; cg.
      epose proof (sidpos_history_period_S Hb Hc Hd H H0).
      assert (N=S T) by lia; subst.
      eapply loop1_nonhalt'; eauto 1.
    + destruct H0c as [H0c|H0c].
      * destruct n; cg.
        epose proof (sidpos_history_period_S Hb Hc Hd H H0).
        assert (N=S T) by lia; subst.
        eapply loop1_nonhalt'; eauto 1.
      * destruct n; cbn in H0c.
        {
          eapply IHls1; eauto 1.
          destruct ls0 as [|h0' ls0'].
          1: destruct N; [lia | cbn in Hb; rewrite skipn_nil in Hb; invst Hb].
          exists h0'. exists ls0'. exists N. exists T.
          repeat split; auto 1; try lia.
          2,3: eapply skipn_S'; eauto 1.
          1: eapply sidpos_history_WF_cdr,Ha.
          destruct N as [|N]. 1: lia.
          epose proof (sidpos_history_period_S' Hd) as Hd'. clear Hd.
          cbn in Hb.
          eapply sidpos_history_period_S; eauto 1.
        }
        {
          eapply IHls1; eauto 1.
          exists h0. exists ls0. exists (S N). exists T.
          repeat split; auto 1; try lia.
          1,2: eapply skipn_S; eauto 1.
          apply (sidpos_history_period_S Hb Hc Hd H H0).
        }
Qed.



Lemma find_loop1_spec tm h0 h1 h2 ls0 ls1 ls2 n:
  sidpos_history_WF tm h0 ls0 ->
  h1::ls1 = skipn (S n) (h0::ls0) ->
  h2::ls2 = skipn (S n) (h1::ls1) ->
  find_loop1 h0 h1 h2 ls0 ls1 ls2 n = true ->
  ~ HaltsFromInit Σ Σ0 tm.
Proof.
  gd n. gd ls2. gd h2. gd h1.
  induction ls1.
  - intros. cbn in H2.
    cbn in H1. rewrite skipn_nil in H1.
    invst H1.
  - intros. cbn in H2.
    repeat rewrite orb_shortcut_spec in H2.
    rewrite Bool.orb_true_iff in H2.
    destruct H2 as [H2|H2].
    + destruct h0 as [es0 d0].
      destruct h1 as [es1 d1].
      destruct h2 as [es2 d2].
      repeat rewrite andb_shortcut_spec in H2.
      repeat rewrite Bool.andb_true_iff in H2.
      destruct H2 as [H2a [H2b [H2c [H2d H2e]]]].
      eapply verify_loop1_spec; eauto 1.
      eexists. eexists. exists 0. eexists.
      repeat split; auto 1.
      unfold sidpos_history_period. intros. lia.
    + destruct ls2 as [|h3 [|h2' ls2']]; cg.
      eapply IHls1; eauto 1.
      * rewrite (skipn_S H0); cg.
      * cbn in H1.
        apply (skipn_S (skipn_S H1)).
Qed.


Lemma find_loop1_0_spec tm h0 h1 ls:
  sidpos_history_WF tm h0 (h1::ls) ->
  find_loop1_0 h0 h1 ls = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  intros.
  unfold find_loop1_0 in H0.
  destruct ls; cg.
  eapply find_loop1_spec; eauto 1; reflexivity.
Qed.



Fixpoint loop1_decider0(tm:TM Σ)(n:nat)(es:ListES)(d:Z)(ls:list (ListES*Z))(n0:nat)(ns:list nat):HaltDecideResult :=
match n with
| O => Result_Unknown
| S n0 =>
  match tm es.(s) es.(m) with
  | None => Result_Halt es.(s) es.(m)
  | Some tr =>
    let es' := ListES_step' tr es in
    let d' := (d+Dir_to_Z tr.(dir _))%Z in
    let ls' := ((es,d)::ls) in
    match n0 with
    | S n0' =>
      loop1_decider0 tm n0 es' d' ls' n0' ns
    | O =>
      if find_loop1_0 (es',d') (es,d) ls then Result_NonHalt else
      loop1_decider0 tm n0 es' d' ls' (hd O ns) (tl ns)
    end
  end
end.

Lemma loop1_decider0_def(tm:TM Σ)(n:nat)(es:ListES)(d:Z)(ls:list (ListES*Z))(n0:nat)(ns:list nat):
loop1_decider0 tm n es d ls n0 ns =
match n with
| O => Result_Unknown
| S n0 =>
  match tm es.(s) es.(m) with
  | None => Result_Halt es.(s) es.(m)
  | Some tr =>
    let es' := ListES_step' tr es in
    let d' := (d+Dir_to_Z tr.(dir _))%Z in
    let ls' := ((es,d)::ls) in
    match n0 with
    | S n0' =>
      loop1_decider0 tm n0 es' d' ls' n0' ns
    | O =>
      if find_loop1_0 (es',d') (es,d) ls then Result_NonHalt else
      loop1_decider0 tm n0 es' d' ls' (hd O ns) (tl ns)
    end
  end
end.
Proof.
  unfold loop1_decider0.
  destruct n; cbn; reflexivity.
Qed.

Lemma sidpos_history_hd {tm es d ls}:
  sidpos_history_WF tm (es,d) ls ->
  MoveDist tm (length ls) (InitES Σ Σ0) (ListES_toES es) d.
Proof.
  unfold sidpos_history_WF.
  intros.
  specialize (H (length ls)).
  replace (length ls - length ls) with 0 in H by lia.
  cbn in H.
  apply H. lia.
Qed.

Lemma s_def l0 r0 m0 s0:
  s {| l:=l0; r:=r0; m:=m0; s:=s0 |} = s0.
Proof.
  reflexivity.
Qed.

Lemma m_def l0 r0 m0 s0:
  m {| l:=l0; r:=r0; m:=m0; s:=s0 |} = m0.
Proof.
  reflexivity.
Qed.

Lemma sidpos_history_WF_S {tm l0 r0 m0 s0 d ls s1 d1 o1}:
  sidpos_history_WF tm (Build_ListES l0 r0 m0 s0, d) ls ->
  tm s0 m0 = Some {| nxt := s1; dir := d1; out := o1 |} ->
  sidpos_history_WF tm (ListES_step' {| nxt := s1; dir := d1; out := o1 |} (Build_ListES l0 r0 m0 s0), (d+(Dir_to_Z d1))%Z) ((Build_ListES l0 r0 m0 s0, d)::ls).
Proof.
  intros.
  epose proof (ListES_step'_spec tm l0 r0 m0 s0) as H1.
  remember (Build_ListES l0 r0 m0 s0) as es0.
  rewrite H0 in H1.
  remember {| nxt := s1; dir := d1; out := o1 |} as tr.
  unfold sidpos_history_WF.
  unfold sidpos_history_WF in H.
  replace (length ((es0, d) :: ls)) with (S (length ls)) by reflexivity.
  intros.
  assert (E:n<=length ls \/ n=S (length ls)) by lia.
  destruct E as [E|E].
  - replace (S (length ls) - n) with (S (length ls - n)) by lia.
    cbn.
    apply H,E.
  - replace (S (length ls) - n) with (O) by lia.
    cbn. rewrite E.
    eassert (H3:_) by (apply (H (length ls)); lia).
    rewrite Nat.sub_diag in H3. cbn in H3.
    subst es0.
    ector; eauto 1.
    subst tr. cbn. lia.
Qed.

Lemma ListES_toES_O:
  (ListES_toES {| l := nil; r := nil; m := Σ0; s := St0 |}) = InitES Σ Σ0.
Proof.
  unfold InitES.
  cbn.
  f_equal.
  fext.
  destruct x.
  1: reflexivity.
  - destruct (Pos.to_nat p).
    1: reflexivity.
    destruct n; reflexivity.
  - destruct (Pos.to_nat p).
    1: reflexivity.
    destruct n; reflexivity.
Qed.

Lemma sidpos_history_WF_O tm:
  sidpos_history_WF tm ({| l := nil; r := nil; m := Σ0; s := St0 |}, 0%Z) nil.
Proof.
  unfold sidpos_history_WF.
  intros.
  cbn in H.
  assert (n=0) by lia. subst.
  replace (length nil - 0) with 0 by reflexivity.
  unfold nth_error.
  rewrite ListES_toES_O.
  ctor.
Qed.

Lemma loop1_decider0_spec tm n es d ls n0 ns:
  sidpos_history_WF tm (es,d) ls ->
  match loop1_decider0 tm n es d ls n0 ns with
  | Result_Halt s0 i0 =>
    exists n1 es0,
    n1<n+(length ls) /\
    HaltsAt Σ tm n1 (InitES Σ Σ0) /\
    Steps Σ tm n1 (InitES Σ Σ0) (ListES_toES es0) /\
    es0.(s)=s0 /\ es0.(m)=i0
  | Result_NonHalt => ~HaltsFromInit Σ Σ0 tm
  | Result_Unknown => True
  end.
Proof.
  gd ns. gd n0. gd ls. gd d. gd es.
  induction n; intros.
  1: cbn; trivial.
  destruct es as [l0 r0 m0 s0] eqn:Ees.
  rewrite loop1_decider0_def.
  rewrite s_def,m_def.
  destruct (tm s0 m0) eqn:E.
  - rewrite <-Ees.
    destruct t as [s1 d1 o1].
    epose proof (sidpos_history_WF_S H E) as H0.
    rewrite <-Ees in H0.
    remember {| nxt := s1; dir := d1; out := o1 |} as t.
    remember (ListES_step' t es) as es'.
    remember (d + Dir_to_Z (dir Σ t))%Z as d'.
    remember ((es, d) :: ls) as ls'.
    destruct n.
    + cbn.
      destruct (find_loop1_0 (es', d') (es, d) ls) eqn:E1.
      2: trivial.
      eapply find_loop1_0_spec; eauto 1.
      rewrite Heqt in Heqd'. cbn in Heqd'. subst d'. subst ls'. apply H0.
    + replace (let es'0 := es' in
      let d'0 := d' in let ls'0 := ls' in loop1_decider0 tm (S n) es'0 d'0 ls'0 n ns) with
      (loop1_decider0 tm (S n) es' d' ls' n ns) by reflexivity.
      specialize (IHn _ _ _ n ns H0).
      rewrite Heqt in Heqd'. cbn in Heqd'. subst d'. subst ls'.
      replace (S n + length ((es, d) :: ls)) with (S (S n) + length ls) in IHn by (cbn; lia).
      apply IHn.
  - exists (length ls). exists es.
    repeat split.
    + lia.
    + eexists.
      split.
      1: apply (MoveDist_Steps (sidpos_history_hd H)).
      unfold step,ListES_toES. rewrite E. reflexivity.
    + subst es. apply (MoveDist_Steps (sidpos_history_hd H)).
    + subst es.  reflexivity.
    + subst es.  reflexivity.
Qed.

Fixpoint halt_decider0(tm:TM Σ)(n:nat)(es:ListES):HaltDecideResult :=
match n with
| O => Result_Unknown
| S n0 =>
  match tm es.(s) es.(m) with
  | None => Result_Halt es.(s) es.(m)
  | Some tr => 
    halt_decider0 tm n0 (ListES_step' tr es)
  end
end.

Lemma halt_decider0_spec tm n es n2:
  Steps Σ tm n2 (InitES Σ Σ0) (ListES_toES es) ->
  match halt_decider0 tm n es with
  | Result_Halt s0 i0 =>
    exists n1 es0,
    n1<n+n2 /\
    HaltsAt Σ tm n1 (InitES Σ Σ0) /\
    Steps Σ tm n1 (InitES Σ Σ0) (ListES_toES es0) /\
    es0.(s)=s0 /\ es0.(m)=i0
  | Result_NonHalt => False
  | Result_Unknown => True
  end.
Proof.
  gd n2. gd es.
  induction n.
  - intros.
    cbn. trivial.
  - intros.
    unfold halt_decider0.
    fold halt_decider0.
    destruct es as [l0 r0 m0 s0].
    unfold l,r,m,s.
    pose proof (ListES_step'_spec tm l0 r0 m0 s0).
    destruct (tm s0 m0) as [tr|] eqn:E.
    + assert (Steps Σ tm (S n2) (InitES Σ Σ0) (ListES_toES (ListES_step' tr {| l := l0; r := r0; m := m0; s := s0 |}))) by (ector; eauto 1).
      specialize (IHn _ _ H1).
      destruct (halt_decider0 tm n (ListES_step' tr {| l := l0; r := r0; m := m0; s := s0 |})).
      * destruct IHn as [n1 [es0 IHn]].
        exists n1. exists es0. destruct es0 as [l2 r2 m2 s2].
        unfold s,m in IHn.
        replace (S n + n2) with (n + S n2) by lia.
        apply IHn.
      * destruct IHn.
      * trivial.
    + exists n2. exists ({| l := l0; r := r0; m := m0; s := s0 |}).
      repeat split.
      * lia.
      * unfold HaltsAt.
        exists (ListES_toES {| l := l0; r := r0; m := m0; s := s0 |}).
        split; auto 1.
      * apply H.
Qed.



Definition halt_decider(n:nat)(tm:TM Σ):HaltDecideResult :=
  halt_decider0 tm n {| l:=nil; r:=nil; m:=Σ0; s:=St0 |}.

Definition loop1_decider(n:nat)(ns:list nat)(tm:TM Σ):HaltDecideResult :=
  loop1_decider0 tm n {| l:=nil; r:=nil; m:=Σ0; s:=St0 |} Z0 nil (hd O ns) (tl ns).


Lemma halt_decider_WF BB n:
  n<=S BB ->
  HaltDecider_WF BB (halt_decider n).
Proof.
  intros.
  unfold HaltDecider_WF,halt_decider.
  intro tm.
  eassert (H0:_). {
    apply (halt_decider0_spec tm n {| l := nil; r := nil; m := Σ0; s := St0 |}).
    rewrite ListES_toES_O.
    ctor.
  }
  destruct (halt_decider0 tm n {| l := nil; r := nil; m := Σ0; s := St0 |}).
  - destruct H0 as [n0 [es0 [H0 [H1 [H2 [H3 H4]]]]]].
    destruct es0 as [l0 r0 m0 s1].
    unfold s,m in H3,H4. subst.
    exists n0. eexists.
    repeat split; eauto 1.
    lia.
  - contradiction.
  - trivial.
Qed.


Lemma loop1_decider_WF BB n ns:
  n<=S BB ->
  HaltDecider_WF BB (loop1_decider n ns).
Proof.
  intros.
  unfold HaltDecider_WF,loop1_decider.
  intro tm.
  eassert (H0:_). {
    apply (loop1_decider0_spec tm n {| l := nil; r := nil; m := Σ0; s := St0 |} 0 nil (hd 0 ns) (tl ns)).
    apply sidpos_history_WF_O.
  }
  destruct (loop1_decider0 tm n {| l := nil; r := nil; m := Σ0; s := St0 |} 0 nil (hd 0 ns) (tl ns)); auto 1.
  cbn in H0.
  destruct H0 as [n1 [es0 [H0 [H1 [H2 [H3 H4]]]]]].
  destruct (ListES_toES es0) as [s1 t0] eqn:E0.
  exists n1. exists t0.
  destruct es0 eqn:E.
  cbn in E0.
  inversion E0. subst s2.
  repeat split; auto 1.
  2: lia. rewrite <-E0 in H2.
  cbn in H3,H4. subst.
  apply H2.
Qed.


Fixpoint ListES_Steps(tm:TM Σ)(n:nat)(es:ListES):option ListES:=
match n with
| O => Some es
| S n0 =>
  match tm es.(s) es.(m) with
  | None => None
  | Some tr =>
    ListES_Steps tm n0 (ListES_step' tr es)
  end
end.

Lemma ListES_Steps_spec tm n es:
  match ListES_Steps tm n es with
  | Some es0 => Steps _ tm n (ListES_toES es) (ListES_toES es0)
  | None => True
  end.
Proof.
  gd es.
  induction n.
  1: intro; cbn; ctor.
  intro.
  cbn.
  destruct (tm (s es) (m es)) as [tr|] eqn:E.
  2: trivial.
  destruct es as [l0 r0 m0 s0].
  cbn in E.
  epose proof (ListES_step'_spec tm l0 r0 m0 s0) as H.
  rewrite E in H.
  specialize (IHn (ListES_step' tr {| l := l0; r := r0; m := m0; s := s0 |})).
  destruct (ListES_Steps tm n (ListES_step' tr {| l := l0; r := r0; m := m0; s := s0 |})).
  2: trivial.
  replace (S n) with (n+1) by lia.
  eapply Steps_trans.
  2: apply IHn.
  ector; eauto 1.
  ctor.
Qed.

Definition halt_time_verifier(tm:TM Σ)(n:nat):bool :=
  match ListES_Steps tm n {| l := nil; r := nil; m := Σ0; s := St0 |} with
  | Some {| l:=_; r:=_; m:=m0; s:=s0 |} =>
    match tm s0 m0 with
    | None => true
    | _ => false
    end
  | None => false
  end.

Lemma halt_time_verifier_spec tm n:
  halt_time_verifier tm n = true ->
  HaltsAt _ tm n (InitES Σ Σ0).
Proof.
  unfold halt_time_verifier,HaltsAt.
  intro H.
  pose proof (ListES_Steps_spec tm n {| l := nil; r := nil; m := Σ0; s := St0 |}).
  destruct (ListES_Steps tm n {| l := nil; r := nil; m := Σ0; s := St0 |}).
  2: cg.
  rewrite ListES_toES_O in H0.
  eexists.
  split.
  - apply H0.
  - destruct l0 as [l0 r0 m0 s0].
    cbn.
    destruct (tm s0 m0); cg.
Qed.

Definition BB:N := 47176869.

Fixpoint nat_eqb_N(n:nat)(m:N) :=
match n,m with
| O,N0 => true
| S n0,Npos _ => nat_eqb_N n0 (N.pred m)
| _,_ => false
end.

Lemma nat_eqb_N_spec n m :
  nat_eqb_N n m = true -> n = N.to_nat m.
Proof.
  gd m.
  induction n; intros.
  - cbn in H.
    destruct m0; cbn; cg.
  - destruct m0.
    + cbn in H. cg.
    + cbn in H.
      specialize (IHn (Pos.pred_N p) H). lia.
Qed.


Definition halt_decider_max := halt_decider 47176870.
Lemma halt_decider_max_spec: HaltDecider_WF (N.to_nat BB) halt_decider_max.
Proof.
  eapply halt_decider_WF.
  unfold BB.
  replace (S (N.to_nat 47176869)) with (N.to_nat 47176870) by lia.
  replace (Init.Nat.of_num_uint
    (Number.UIntDecimal
       (Decimal.D4
          (Decimal.D7
             (Decimal.D1
                (Decimal.D7 (Decimal.D6 (Decimal.D8 (Decimal.D7 (Decimal.D0 Decimal.Nil))))))))))
  with (N.to_nat 47176870).
  1: apply Nat.le_refl.
  symmetry.
  apply nat_eqb_N_spec.
  vm_compute.
  reflexivity.
Time Qed.

Definition BB5_champion := (makeTM BR1 CL1 CR1 BR1 DR1 EL0 AL1 DL1 HR1 AL0).

Lemma BB5_lower_bound:
  exists tm,
  HaltsAt _ tm (N.to_nat BB) (InitES Σ Σ0).
Proof.
  exists BB5_champion.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Time Qed.


Definition decider0 := HaltDecider_nil.
Definition decider1 := halt_decider 130.
Definition decider2 := (loop1_decider 130 (1::2::4::8::16::32::64::128::256::512::nil)).

Definition decider3 := (NGramCPS_decider_impl2 1 1 100).
Definition decider4 := (NGramCPS_decider_impl2 2 2 200).
Definition decider5 := (NGramCPS_decider_impl2 3 3 400).
Definition decider6 := (NGramCPS_decider_impl1 2 2 2 1600).
Definition decider7 := (NGramCPS_decider_impl1 2 3 3 1600).

Definition decider8 := (loop1_decider 4100 (1::2::4::8::16::32::64::128::256::512::1024::2048::4096::nil)).

Definition decider9 := (NGramCPS_decider_impl1 4 2 2 600).
Definition decider10 := (NGramCPS_decider_impl1 4 3 3 1600).
Definition decider11 := (NGramCPS_decider_impl1 6 2 2 3200).
Definition decider12 := (NGramCPS_decider_impl1 6 3 3 3200).
Definition decider13 := (NGramCPS_decider_impl1 8 2 2 1600).
Definition decider14 := (NGramCPS_decider_impl1 8 3 3 1600).

Lemma decider2_WF: HaltDecider_WF (N.to_nat BB) decider2.
Proof.
  apply loop1_decider_WF.
  unfold BB.
  lia.
Qed.

Lemma root_q_WF:
  SearchQueue_WF (N.to_nat BB) root_q root.
Proof.
  apply SearchQueue_init_spec,root_WF.
Qed.

Definition root_q_upd1:=
  (SearchQueue_upd root_q decider2).

Lemma root_q_upd1_WF:
  SearchQueue_WF (N.to_nat BB) root_q_upd1 root.
Proof.
  apply SearchQueue_upd_spec.
  - apply root_q_WF.
  - apply decider2_WF.
Qed.

Definition first_trans_is_R(x:TNF_Node):bool :=
  match x.(TNF_tm) St0 Σ0 with
  | Some {| nxt:=_; dir:=Dpos; out:=_ |} => true
  | _ => false
  end.

Definition root_q_upd1_simplified:SearchQueue:=
  (filter first_trans_is_R (fst root_q_upd1), nil).

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
  SearchQueue_WF (N.to_nat BB) root_q_upd1_simplified root.
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

Fixpoint length_tailrec0{T}(ls:list T)(n:N):N :=
match ls with
| nil => n
| h::t => length_tailrec0 t (N.succ n)
end.
Definition length_tailrec{T}(ls:list T):N := length_tailrec0 ls 0.


Definition St_to_N(s1:St):N :=
match s1 with
| St0 => 1
| St1 => 2
| St2 => 3
| St3 => 4
| St4 => 5
end.

Definition Dir_to_N(d1:Dir):N :=
match d1 with
| Dpos => 1
| Dneg => 0
end.

Definition Σ_to_N(o1:Σ):N :=
match o1 with
| Σ0 => 0
| Σ1 => 1
end.

Definition Trans_to_N(tr:Trans Σ):list (N*N) :=
let (s1,d1,o1):=tr in
((St_to_N s1,6)::(Σ_to_N o1,2)::(Dir_to_N d1,2)::nil)%N.

Definition option_Trans_to_N(tr:option (Trans Σ)):list (N*N) :=
match tr with
| None =>
  ((0,6)::(Σ_to_N Σ1,2)::(Dir_to_N Dpos,2)::nil)%N
| Some tr => Trans_to_N tr
end.

Fixpoint TM_to_N_0(ls:list (N*N))(v:N):N :=
match ls with
| nil => v
| (a,b)::t => TM_to_N_0 t (v*b+a)
end.

Definition TM_to_N(tm:TM Σ):N :=
  TM_to_N_0 (
  (option_Trans_to_N (tm St0 Σ0))++
  (option_Trans_to_N (tm St0 Σ1))++
  (option_Trans_to_N (tm St1 Σ0))++
  (option_Trans_to_N (tm St1 Σ1))++
  (option_Trans_to_N (tm St2 Σ0))++
  (option_Trans_to_N (tm St2 Σ1))++
  (option_Trans_to_N (tm St3 Σ0))++
  (option_Trans_to_N (tm St3 Σ1))++
  (option_Trans_to_N (tm St4 Σ0))++
  (option_Trans_to_N (tm St4 Σ1))++nil
  ) 0.

Definition TNF_Node_list_to_N_list := map (fun (x:TNF_Node) => TM_to_N (TNF_tm x)).


Compute (TM_to_N (makeTM BR1 HR1 CL0 ER0 DL0 CL1 AR1 BR0 DR0 DR1)).


End ListTape.



Module MacroMachine.

Import ListTape.

Section MacroMachine_secion.

Definition Word := list Σ.

Record RepeatWord := {
  w: Word;
  min_cnt: nat;
  is_const: bool;
}.

Inductive RepW_match:RepeatWord->Word->Prop :=
| RepW_match_O w0:
  RepW_match {| w:=w0; min_cnt:=0; is_const:=true |} nil
| RepW_match_S0 w0 w1 n:
  RepW_match {| w:=w0; min_cnt:=n; is_const:=true |} w1 ->
  RepW_match {| w:=w0; min_cnt:=S n; is_const:=true |} (w0++w1)
| RepW_match_S1 w0 w1 n n0:
  n<=n0 ->
  RepW_match {| w:=w0; min_cnt:=n0; is_const:=true |} w1 ->
  RepW_match {| w:=w0; min_cnt:=n; is_const:=false |} w1
.

Inductive RepWL_match:(list RepeatWord)->(nat->Σ)->Prop :=
| RepWL_match_O:
  RepWL_match nil half_tape_all0
| RepWL_match_S h t fh ft:
  RepW_match h fh ->
  RepWL_match t ft ->
  RepWL_match (h::t) (app_halftape fh ft)
.




Record RepeatWordList_ES := {
  l: list RepeatWord;
  r: list RepeatWord;
  s: St;
  sgn: Dir;
}.



Fixpoint all0(x:Word):bool :=
match x with
| nil => true
| Σ0::t => all0 t
| _::t => false
end.

Lemma all0_spec x:
  all0 x = true -> x = repeat Σ0 (length x).
Proof.
  induction x; cbn; intros.
  - reflexivity.
  - destruct a eqn:E in H. 2: cg.
    rewrite <-IHx; auto 1. cg.
Qed.


Fixpoint Word_eqb(x1 x2:Word):bool :=
match x1,x2 with
| nil,nil => true
| h1::t1,h2::t2 =>
  if Σ_eqb h1 h2 then Word_eqb t1 t2 else false
| _,_ => false
end.

Lemma Word_eqb_spec x1 x2:
  if Word_eqb x1 x2 then x1=x2 else x1<>x2.
Proof.
  gd x2.
  induction x1 as [|h1 t1]; cbn; intros; destruct x2 as [|h2 t2]; cg.
  destruct (Σ_eqb h1 h2) eqn:E.
  - specialize (IHt1 t2).
    destruct (Word_eqb t1 t2); cg.
    pose proof (Σ_eqb_spec h1 h2).
    rewrite E in H.
    cg.
  - pose proof (Σ_eqb_spec h1 h2).
    rewrite E in H.
    cg.
Qed.


Hypothesis len:nat.

Definition pop(wl:list RepeatWord): option (Word*(list (list RepeatWord))) :=
  match wl with
  | nil => Some (repeat Σ0 len,(nil)::nil)
  | v::wl0 =>
    match min_cnt v with
    | O => None
    | S n0 => Some
      (w v,(match n0 with
      | S _ => ({| w:=w v; min_cnt:=n0; is_const:=true |}::wl0)
      | O => (wl0)
      end)::(if (is_const v) then nil else ((wl)::nil)))
    end
  end.

Lemma app_half_tape_all0 n:
  half_tape_all0 = app_halftape (repeat Σ0 n) half_tape_all0.
Proof.
  fext. unfold half_tape_all0,app_halftape.
  assert (x<n\/n<=x) by lia.
  destruct H as [H|H].
  - rewrite nth_error_repeat; auto 1.
  - rewrite <-(repeat_length Σ0 n) in H.
    rewrite <-nth_error_None in H.
    rewrite H.
    reflexivity.
Qed.

Lemma pop_spec wl:
  match pop wl with
  | None => True
  | Some (w,ls) =>
    forall f,
      RepWL_match wl f ->
      ((exists wl0 f1, In wl0 ls /\ RepWL_match wl0 f1 /\ f = app_halftape w f1))
  end.
Proof.
  unfold pop.
  destruct wl as [|v wl0].
  - intros.
    exists nil. exists half_tape_all0.
    cbn.
    repeat split.
    + tauto.
    + ctor.
    + invst H.
      apply app_half_tape_all0.
  - destruct v as [w0 mc isc]; cbn.
    destruct mc as [|mc].
    1: auto 1.
    intros.
    invst H.
    invst H2.
    + eexists.
      exists (app_halftape w2 ft).
      split. 1: left; reflexivity.
      split.
      * destruct mc as [|mc].
        -- invst H6. rewrite app_halftape_nil. apply H4.
        -- ector; eauto 1.
      * rewrite app_halftape_assoc; reflexivity.
    + destruct n0 as [|n0]. 1: lia.
      invst H7.
      assert (E:mc = n0 \/ S mc <= n0) by lia.
      destruct E as [E|E].
      -- subst n0.
        eexists.
        exists (app_halftape w2 ft).
        split. 1: left; reflexivity.
        split.
        * destruct mc as [|mc].
          ++ invst H5. rewrite app_halftape_nil. apply H4.
          ++ ector; eauto 1.
        * rewrite app_halftape_assoc; reflexivity.
      -- eexists.
        exists (app_halftape w2 ft).
        split. 1: right; left; reflexivity.
        split.
        * ector; eauto 1. ector; eauto 1.
        * rewrite app_halftape_assoc; reflexivity.
Qed.

Ltac Word_eq_dec s1 s2 := eq_dec Word_eqb_spec Word_eqb s1 s2.

Lemma nat_lt_spec x1 x2:
  if x1 <? x2 then x1<x2 else x2<=x1.
Proof.
  destruct (Nat.ltb_spec x1 x2); auto 1.
Qed.

Ltac nat_lt_dec s1 s2 := eq_dec nat_lt_spec Nat.ltb s1 s2.

Hypothesis min_nonconst_len:nat.

Definition push(wl:list RepeatWord)(w0:Word) :=
match wl with
| v0::wl0 =>
  if Word_eqb (w v0) w0 then
    let cnt := S (min_cnt v0) in
    (if Nat.ltb cnt min_nonconst_len then
    {| w:=w0; min_cnt:=cnt; is_const:=(is_const v0) |}
    else
    {| w:=w0; min_cnt:=min_nonconst_len; is_const:=false |})::wl0
  else
    {| w:=w0; min_cnt:=1; is_const:=true |}::wl
| nil =>
  if all0 w0 then nil else {| w:=w0; min_cnt:=1; is_const:=true |}::wl
end.


Lemma push_spec wl w0:
  forall f,
  RepWL_match wl f ->
  RepWL_match (push wl w0) (app_halftape w0 f).
Proof.
  intros.
  unfold push.
  destruct wl as [|v0 wl0].
  - destruct (all0 w0) eqn:E.
    + invst H.
      rewrite (all0_spec _ E).
      rewrite <-app_half_tape_all0.
      ctor.
    + invst H.
      ector; eauto 1.
      rewrite <-app_nil_r.
      ctor; ctor.
  - destruct v0 as [w1 mc isc]; unfold w,min_cnt,is_const.
    Word_eq_dec w1 w0.
    + subst.
      nat_lt_dec (S mc) min_nonconst_len.
      * invst H.
        rewrite app_halftape_assoc.
        ctor; auto 1.
        destruct isc.
        -- ctor; auto 1.
        -- invst H3.
           ector. 2: ector; eauto 1. lia.
      * invst H.
        rewrite app_halftape_assoc.
        ctor; auto 1.
        destruct isc.
        -- ector. 2: ector; eauto 1. auto 1.
        -- invst H3. ector. 2: ector; eauto 1. lia.
    + ctor; auto 1. rewrite <-app_nil_r. ctor; ctor.
Qed.


Definition WordUpdate_step0(tm:TM Σ)(x:ListES):option (ListES*(option Dir)) :=
let (l0,r0,m0,s0):=x in
match tm s0 m0 with
| None => None
| Some tr =>
  let (s1,d,o) := tr in
    Some
    match d with
    | Dpos =>
      match r0 with
      | m1::r1 => (Build_ListES (o::l0) r1 m1 s1,None)
      | nil => (Build_ListES l0 nil o s1,Some Dpos)
      end
    | Dneg =>
      match l0 with
      | m1::l1 => (Build_ListES l1 (o::r0) m1 s1,None)
      | nil => (Build_ListES nil r0 o s1,Some Dneg)
      end
    end
end.

Lemma app_halftape_cdr'' L:
  app_halftape ((L 0)::nil) (half_tape_cdr L)=L.
Proof.
  rewrite <-app_halftape_nil,app_halftape_cdr.
  reflexivity.
Qed.

Lemma make_tape'_split_l l2 l1 l0 m0 r0 r1:
  make_tape' (app_halftape l2 l1) l0 m0 r0 r1 =
  make_tape' l1 (l0++l2) m0 r0 r1.
Proof.
  unfold make_tape'.
  f_equal.
  apply app_halftape_assoc.
Qed.

Lemma make_tape'_split_r r2 l1 l0 m0 r0 r1:
  make_tape' l1 l0 m0 r0 (app_halftape r2 r1) =
  make_tape' l1 l0 m0 (r0++r2) r1.
Proof.
  unfold make_tape'.
  f_equal.
  apply app_halftape_assoc.
Qed.

Lemma WordUpdate_step0_spec tm (x:ListES):
  let (l0,r0,m0,s0):=x in
  match WordUpdate_step0 tm x with
  | None => True
  | Some (x1,None) =>
    AbstractSteps tm 1 x x1
  | Some (x1,Some Dpos) =>
    let (l1,r1,m1,s1):=x1 in
    length l0 + length r0 = length l1 + length r1 /\
    forall L R,
    Steps Σ tm 1 (makeES x L R) (s1,make_tape' L (m1::l1) (R 0) nil (half_tape_cdr R))
  | Some (x1,Some Dneg) =>
    let (l1,r1,m1,s1):=x1 in
    length l0 + length r0 = length l1 + length r1 /\
    forall L R,
    Steps Σ tm 1 (makeES x L R) (s1,make_tape' (half_tape_cdr L) nil (L 0) (m1::r1) R)
  end.
Proof.
  destruct x as [l0 r0 m0 s0].
  cbn.
  destruct (tm s0 m0) as [[s1 d o]|] eqn:E.
  destruct d.
  - destruct l0.
    + cbn. split. 1: auto.
      intros.
      ector.
      1: ctor.
      cbn.
      rewrite E.
      f_equal. f_equal.
      rewrite make_tape'_upd.
      replace (make_tape' L nil o r0 R) with (make_tape' (app_halftape ((L 0)::nil) (half_tape_cdr L)) nil o r0 R).
      2: f_equal; apply app_halftape_cdr''.
      rewrite make_tape'_split_l. cbn.
      apply make_tape'_mov_l.
    + split; cbn.
      1: lia.
      intros.
      ector.
      1: ctor.
      cbn.
      rewrite E.
      f_equal. f_equal.
      rewrite make_tape'_upd.
      apply make_tape'_mov_l.
  - destruct r0.
    + cbn. split. 1: auto.
      intros.
      ector.
      1: ctor.
      cbn.
      rewrite E.
      f_equal. f_equal.
      rewrite make_tape'_upd.
      replace (make_tape' L l0 o nil R) with (make_tape' L l0 o nil (app_halftape ((R 0)::nil) (half_tape_cdr R))).
      2: f_equal; apply app_halftape_cdr''.
      rewrite make_tape'_split_r. cbn.
      apply make_tape'_mov_r.
    + split; cbn.
      1: lia.
      intros.
      ector.
      1: ctor.
      cbn.
      rewrite E.
      f_equal. f_equal.
      rewrite make_tape'_upd.
      apply make_tape'_mov_r.
  - trivial.
Qed.


Fixpoint WordUpdate_steps(tm:TM Σ)(x:ListES)(n:nat):option (ListES*Dir) :=
match n with
| O => None
| S n0 =>
  match WordUpdate_step0 tm x with
  | Some (x0,None) => WordUpdate_steps tm x0 n0
  | Some (x0,Some d) => Some (x0,d)
  | None => None
  end
end.


Lemma WordUpdate_steps_spec tm (x:ListES) n0:
  let (l0,r0,m0,s0):=x in
  match WordUpdate_steps tm x n0 with
  | None => True
  | Some (x1,Dpos) =>
    let (l1,r1,m1,s1):=x1 in
    length l0 + length r0 = length l1 + length r1 /\
    exists n,
    forall L R,
    Steps Σ tm (S n) (makeES x L R) (s1,make_tape' L (m1::l1) (R 0) nil (half_tape_cdr R))
  | Some (x1,Dneg) =>
    let (l1,r1,m1,s1):=x1 in
    length l0 + length r0 = length l1 + length r1 /\
    exists n,
    forall L R,
    Steps Σ tm (S n) (makeES x L R) (s1,make_tape' (half_tape_cdr L) nil (L 0) (m1::r1) R)
  end.
Proof.
  gd x.
  induction n0; intros.
  - cbn.
    destruct x as [l0 r0 m0 s0].
    trivial.
  - destruct x as [l0 r0 m0 s0].
    unfold WordUpdate_steps.
    pose proof (WordUpdate_step0_spec tm (Build_ListES l0 r0 m0 s0)) as H.
    destruct (WordUpdate_step0 tm (Build_ListES l0 r0 m0 s0)) as [[x1 d1]|].
    2: trivial.
    destruct d1 as [d1|].
    + destruct x1 as [l1 r1 m1 s1].
      destruct d1;
        (split; [ tauto | exists 0; tauto ]).
    + fold WordUpdate_steps.
      specialize (IHn0 x1).
      destruct x1 as [l1 r1 m1 s1].
      cbn in IHn0.
      destruct H as [Ha Hb]. cbn in Ha,Hb.
      destruct (WordUpdate_steps tm (Build_ListES l1 r1 m1 s1) n0) as [[x2 [|]]|]. 3: trivial.
      1,2: destruct x2 as [l2 r2 m2 s2];
        destruct IHn0 as [I1 [n I2]];
        split; [ cg |
          exists (S n);
          replace (S (S n)) with ((S n)+1) by lia;
          intros; eapply Steps_trans; eauto 1].
Qed.

Hypothesis WordUpdate_MAXT:nat.



Definition WordUpdate(tm:TM Σ)(s0:St)(w0:Word)(sgn0:Dir):option (St*Word*bool) :=
match w0 with
| nil => None
| m0::w1 =>
  match
    match sgn0 with
    | Dpos => WordUpdate_steps tm (Build_ListES nil w1 m0 s0) WordUpdate_MAXT
    | Dneg => WordUpdate_steps tm (Build_ListES w1 nil m0 s0) WordUpdate_MAXT
    end
  with
  | None => None
  | Some (Build_ListES l1 r1 m1 s1,d) =>
    match d with
    | Dpos => Some (s1,m1::l1,negb (Dir_eqb sgn0 d))
    | Dneg => Some (s1,m1::r1,negb (Dir_eqb sgn0 d))
    end
  end
end.


Definition make_tape'' l1 w1 r1 (sgn1:Dir):=
match w1 with
| m1::w2 =>
  match sgn1 with
  | Dpos => make_tape' l1 nil m1 w2 r1
  | Dneg => make_tape' r1 w2 m1 nil l1
  end
| nil =>
  match sgn1 with
  | Dpos => make_tape' l1 nil (r1 0) nil (half_tape_cdr r1)
  | Dneg => make_tape' (half_tape_cdr r1) nil (r1 0) nil l1
  end
end.

Lemma WordUpdate_spec tm s0 w0 sgn0:
  match WordUpdate tm s0 w0 sgn0 with
  | None => True
  | Some (s1,w1,is_back) =>
    forall L R,
      exists n,
        if is_back then
          Steps Σ tm (S n) (s0,make_tape'' L w0 R sgn0) (s1,(make_tape'' (app_halftape w1 R) nil L (Dir_rev sgn0)))
        else
          Steps Σ tm (S n) (s0,make_tape'' L w0 R sgn0) (s1,make_tape'' (app_halftape w1 L) nil R sgn0)
  end.
Proof.
  unfold WordUpdate.
  destruct w0 as [|m0 w1].
  1: trivial.
  destruct sgn0.
  {
    pose proof (WordUpdate_steps_spec tm (Build_ListES w1 nil m0 s0) WordUpdate_MAXT) as H.
    cbn in H.
    destruct (WordUpdate_steps tm (Build_ListES w1 nil m0 s0) WordUpdate_MAXT) as [[x1 d]|].
    2: trivial.
    destruct x1 as [l1 r1 m1 s1].
    destruct d;
      intros; cbn;
      destruct H as [Ha [n Hb]];
      exists n.
    - rewrite make_tape'_split_r.
      apply Hb.
    - rewrite make_tape'_split_l.
      apply Hb.
  }
  {
    pose proof (WordUpdate_steps_spec tm (Build_ListES nil w1 m0 s0) WordUpdate_MAXT) as H.
    cbn in H.
    destruct (WordUpdate_steps tm (Build_ListES nil w1 m0 s0) WordUpdate_MAXT) as [[x1 d]|].
    2: trivial.
    destruct x1 as [l1 r1 m1 s1].
    destruct d;
      intros; cbn;
      destruct H as [Ha [n Hb]];
      exists n.
    - rewrite make_tape'_split_r.
      apply Hb.
    - rewrite make_tape'_split_l.
      apply Hb.
  }
Qed.

Definition RepWL_step00(tm:TM Σ)(x:RepeatWordList_ES)(w0:Word)(r1:list RepeatWord):=
  let (l0,_,s0,sgn0):=x in
    match WordUpdate tm s0 w0 sgn0 with
    | None => None
    | Some (s1,w1,is_back) =>
        if is_back
        then Some {| l:=push r1 w1; r:=l0; s:=s1; sgn:=Dir_rev sgn0 |}
        else Some {| l:=push l0 w1; r:=r1; s:=s1; sgn:=sgn0 |}
    end.

Fixpoint RepWL_step0(tm:TM Σ)(x:RepeatWordList_ES)(w0:Word)(ls:list (list RepeatWord)):option (list RepeatWordList_ES) :=
  match ls with
  | nil => Some nil
  | r1::ls0 =>
    match RepWL_step00 tm x w0 r1 with
    | None => None
    | Some x1 =>
      match RepWL_step0 tm x w0 ls0 with
      | None => None
      | Some ret => Some (x1::ret)
      end
    end
  end.


Definition RepWL_step(tm:TM Σ)(x:RepeatWordList_ES) :=
  let (l0,r0,s0,sgn0):=x in
  match pop r0 with
  | None => None
  | Some (w0,ls) =>
    RepWL_step0 tm x w0 ls
  end.



Inductive In_RepWL_ES:(ExecState Σ)->RepeatWordList_ES->Prop :=
| In_RepWL_ES_intro l1 r1 l0 r0 s0 sgn0:
  RepWL_match l0 l1 ->
  RepWL_match r0 r1 ->
  In_RepWL_ES (s0,make_tape'' l1 nil r1 sgn0) (Build_RepeatWordList_ES l0 r0 s0 sgn0)
.


Definition push'(wl:list RepeatWord)(w0:Word):=
  {| w := w0; min_cnt := 1; is_const := true |} :: wl.

Definition halftape_skipn(n:nat)(f:nat->Σ):nat->Σ :=
  fun m => f (n+m).

Lemma app_halftape_skipn_cdr c w0 f:
app_halftape w0
  (halftape_skipn (S (length w0)) (app_halftape (c :: w0) f)) =
half_tape_cdr (app_halftape (c :: w0) f).
Proof.
  fext.
  unfold app_halftape,halftape_skipn,half_tape_cdr.
  replace (S (length w0) + (x - length w0)) with (S ((length w0) + (x - length w0))) by lia.
  cbn.
  destruct (nth_error w0 x) eqn:E; auto 1.
  rewrite nth_error_None in E.
  replace ((length w0 + (x - length w0))) with x by lia.
  rewrite <-nth_error_None in E.
  rewrite E.
  reflexivity.
Qed.

Lemma app_halftape_skipn w0 f:
  (halftape_skipn (length w0) (app_halftape w0 f)) = f.
Proof.
  fext.
  unfold halftape_skipn,app_halftape.
  assert (length w0 <= length w0 + x) by lia.
  rewrite <-nth_error_None in H.
  rewrite H.
  f_equal.
  lia.
Qed.


Lemma halftape_skipn_0 f:
  halftape_skipn 0 f = f.
Proof.
  fext.
  reflexivity.
Qed.

Lemma RepWL_step00_spec tm x w0 r0:
  match RepWL_step00 tm x w0 r0 with
  | None => True
  | Some x1 =>
  let (l0,_,s0,sgn0):=x in
    forall st0, In_RepWL_ES st0 {| l:=l0; r:=push' r0 w0; s:=s0; sgn:=sgn0 |} ->
    exists n st1, (Steps Σ tm (1+n) st0 st1 /\ In_RepWL_ES st1 x1)
  end.
Proof.
unfold RepWL_step00.
destruct x as [l0 r0' s0 sgn0].
pose proof (WordUpdate_spec tm s0 w0 sgn0).
destruct (WordUpdate tm s0 w0 sgn0) as [[[s1 w1] d1]|].
2: trivial.
destruct d1 eqn:Ed1.
- intros.
  destruct st0 as [s0' t0'].
  invst H0.
  destruct sgn0.
  + specialize (H l1 (halftape_skipn (length w0) r1)).
    destruct H as [n H]. cbn. cbn in H.
    exists n.
    exists (s1, make_tape'' (app_halftape w1 (halftape_skipn (length w0) r1)) nil 
        (l1) Dpos).
    split.
    * unfold make_tape'' in H.
      destruct w0;
      cbn in H.
      ++ apply H.
      ++ replace (make_tape' (half_tape_cdr r1) nil (r1 0) nil l1) with
        (make_tape' (halftape_skipn (S (length w0)) r1) w0 σ nil l1).
        apply H.
        unfold make_tape'.
        invst H8.
        invst H3.
        rewrite <-app_halftape_assoc.
        cbn.
        f_equal.
        rewrite app_halftape_nil.
        apply app_halftape_skipn_cdr.
    * ector; eauto 1.
      invst H8. invst H3. invst H7.
      rewrite app_nil_r.
      apply push_spec.
      rewrite app_halftape_skipn.
      apply H6.
  + specialize (H l1 (halftape_skipn (length w0) r1)).
    destruct H as [n H]. cbn. cbn in H.
    exists n.
    exists (s1, make_tape'' (app_halftape w1 (halftape_skipn (length w0) r1)) nil 
        (l1) Dneg).
    split.
    * unfold make_tape'' in H.
      destruct w0;
      cbn in H.
      ++ rewrite halftape_skipn_0 in H.
        rewrite halftape_skipn_0.
        unfold make_tape''.
        apply H.
      ++ replace (make_tape' l1 nil (r1 0) nil (half_tape_cdr r1)) with
        (make_tape' l1 nil σ w0 (halftape_skipn (S (length w0)) r1)).
        apply H.
        unfold make_tape'.
        invst H8.
        invst H3.
        rewrite <-app_halftape_assoc.
        cbn.
        f_equal.
        rewrite app_halftape_nil.
        apply app_halftape_skipn_cdr.
    * ector; eauto 1.
      invst H8. invst H3. invst H7.
      rewrite app_nil_r.
      apply push_spec.
      rewrite app_halftape_skipn.
      apply H6.
- intros.
  destruct st0 as [s0' t0'].
  invst H0.
  destruct sgn0.
  + specialize (H l1 (halftape_skipn (length w0) r1)).
    destruct H as [n H]. cbn. cbn in H.
    exists n.
    exists (s1, make_tape'' (app_halftape w1 l1) nil (halftape_skipn (length w0) r1)
        Dneg).
    split.
    * unfold make_tape'' in H.
      destruct w0;
      cbn in H.
      ++ rewrite halftape_skipn_0 in H.
        rewrite halftape_skipn_0.
        unfold make_tape''.
        apply H.
      ++ replace (make_tape' (half_tape_cdr r1) nil (r1 0) nil l1) with (make_tape' (halftape_skipn (S (length w0)) r1) w0 σ nil l1).
        apply H.
        unfold make_tape'.
        repeat rewrite app_halftape_nil.
        invst H8. invst H3.
        rewrite <-app_halftape_assoc.
        cbn.
        f_equal.
        apply app_halftape_skipn_cdr.
    * invst H8. invst H3. invst H7.
      ector; eauto 1.
      -- apply push_spec,H4.
      -- rewrite app_nil_r,app_halftape_skipn.
         apply H6.
  + specialize (H l1 (halftape_skipn (length w0) r1)).
    destruct H as [n H]. cbn. cbn in H.
    exists n.
    exists (s1, make_tape'' (app_halftape w1 l1) nil (halftape_skipn (length w0) r1)
        Dpos).
    split.
    * unfold make_tape'' in H.
      destruct w0;
      cbn in H.
      ++ rewrite halftape_skipn_0 in H.
        rewrite halftape_skipn_0.
        unfold make_tape''.
        apply H.
      ++ replace (make_tape' l1 nil (r1 0) nil (half_tape_cdr r1)) with 
          (make_tape' l1 nil σ w0 (halftape_skipn (S (length w0)) r1)).
        apply H.
        unfold make_tape'.
        repeat rewrite app_halftape_nil.
        invst H8. invst H3.
        rewrite <-app_halftape_assoc.
        cbn.
        f_equal.
        apply app_halftape_skipn_cdr.
    * invst H8. invst H3. invst H7.
      ector; eauto 1.
      -- apply push_spec,H4.
      -- rewrite app_nil_r,app_halftape_skipn.
         apply H6.
Qed.

Lemma RepWL_step0_spec tm x w0 r0:
  match RepWL_step0 tm x w0 r0 with
  | None => True
  | Some x1 =>
  let (l0,_,s0,sgn0):=x in
    forall st0, (exists r1, In r1 r0 /\ In_RepWL_ES st0 {| l:=l0; r:=push' r1 w0; s:=s0; sgn:=sgn0 |}) ->
    exists n st1 x2, (Steps Σ tm (1+n) st0 st1 /\ In_RepWL_ES st1 x2 /\ In x2 x1)
  end.
Proof.
  induction r0.
  - cbn.
    destruct x as [l0 r0' s0 sgn0].
    intros.
    destruct H as [n1 [Ha Hb]].
    contradiction.
  - cbn.
    pose proof (RepWL_step00_spec tm x w0 a) as H.
    destruct (RepWL_step00 tm x w0 a).
    2: trivial.
    destruct (RepWL_step0 tm x w0 r0).
    2: trivial.
    destruct x as [l1 r0' s0 sgn0].
    intros.
    destruct H0 as [r2 [H0a H0b]].
    destruct H0a as [H0a|H0a].
    + subst a. specialize (H st0 H0b).
      destruct H as [n [st1 [Ha Hb]]].
      exists n. exists st1. eexists.
      repeat split; eauto 1.
      left. reflexivity.
    + specialize (IHr0 st0).
      eassert (H1:_). {
        apply IHr0.
        eexists.
        split; eauto 1.
      }
      destruct H1 as [n [st1 [x2 [H1a [H1b H1c]]]]].
      exists n. exists st1. exists x2.
      repeat split; auto 1. right. auto 1.
Qed.



Lemma RepWL_step_spec tm x:
  match RepWL_step tm x with
  | None => True
  | Some ls =>
    forall st0, In_RepWL_ES st0 x ->
    exists n st1 x1, (Steps Σ tm (1+n) st0 st1 /\ In_RepWL_ES st1 x1 /\ In x1 ls)
  end.
Proof.
  unfold RepWL_step.
  destruct x as [l0 r0 s0 sgn0].
  pose proof (pop_spec r0) as H0.
  destruct (pop r0) as [[w0 ls]|] eqn:E.
  2: trivial.
  pose proof (RepWL_step0_spec tm {| l := l0; r := r0; s := s0; sgn := sgn0 |} w0 ls) as H.
  destruct (RepWL_step0 tm {| l := l0; r := r0; s := s0; sgn := sgn0 |} w0 ls).
  2: trivial.
  intros.
  specialize (H st0).
  apply H.
  invst H1.

  specialize (H0 _ H8).
  destruct H0 as [wl0 [f1 [H0a [H0b H0c]]]].
  exists wl0.
  repeat split; auto 1.
  rewrite H0c.
  ector; eauto 1.
  rewrite <-app_nil_r.
  ctor. ctor.
Qed.


Definition Dir_enc(d:Dir):=
match d with
| Dpos => xI xH
| Dneg => xH
end.

Lemma Dir_enc_inj: is_inj Dir_enc.
Proof.
  intros x1 x2 H.
  destruct x1,x2; cbn in H; cg.
Qed.

Definition bool_enc(x:bool):=
  if x then xI xH else xH.

Lemma bool_enc_inj: is_inj bool_enc.
Proof.
  intros x1 x2 H.
  destruct x1,x2; cbn in H; cg.
Qed.

Definition RepeatWord_enc(x:RepeatWord):positive :=
  let (w0,mc,isc):=x in
  enc_list ((listΣ_enc w0)::(Pos.of_succ_nat mc)::(bool_enc isc)::nil).

Lemma RepeatWord_enc_inj: is_inj RepeatWord_enc.
Proof.
  intros x1 x2 H.
  destruct x1,x2.
  epose proof (enc_list_inj _ _ H).
  invst H0.
  f_equal.
  - apply listΣ_inj; auto 1.
  - lia.
  - apply bool_enc_inj; auto 1.
Qed.

Definition list_enc{T}(T_enc:T->positive)(ls:list T) :=
  enc_list (map T_enc ls).

Lemma list_enc_inj{T}(T_enc:T->positive):
  is_inj T_enc ->
  is_inj (list_enc T_enc).
Proof.
  intros H0 x1.
  induction x1 as [|h1 x1]; intros x2 H.
  - unfold list_enc in H.
    epose proof (enc_list_inj _ _ H) as H1.
    cbn in H1.
    destruct x2; cbn in H1; cg.
  - destruct x2 as [|h2 x2].
    + epose proof (enc_list_inj _ _ H) as H1.
      invst H1.
    + epose proof (enc_list_inj _ _ H) as H1.
      cbn in H1.
      invst H1.
      f_equal.
      * apply H0; auto 1.
      * apply IHx1.
        unfold list_enc.
        cg.
Qed.

Definition RepWL_ES_enc(x:RepeatWordList_ES):positive :=
let (l0,r0,s0,sgn0):=x in
enc_list ((Dir_enc sgn0)::(St_enc s0)::(list_enc RepeatWord_enc l0)::(list_enc RepeatWord_enc r0)::nil).

Lemma RepWL_ES_enc_inj: is_inj RepWL_ES_enc.
Proof.
  intros x1 x2 H.
  destruct x1,x2.
  epose proof (enc_list_inj _ _ H).
  invst H0.
  f_equal.
  - eapply list_enc_inj; eauto 1.
    apply RepeatWord_enc_inj.
  - eapply list_enc_inj; eauto 1.
    apply RepeatWord_enc_inj.
  - apply St_enc_inj; auto 1.
  - apply Dir_enc_inj; auto 1.
Qed.


Definition RepWL_InitES :=
  {| l:=nil; r:=nil; s:=St0; sgn:=Dpos |}.

Lemma In_RepWL_ES_InitES:
  In_RepWL_ES (InitES Σ Σ0) RepWL_InitES.
Proof.
  unfold RepWL_InitES.
  replace (InitES Σ Σ0) with (St0,make_tape'' half_tape_all0 nil half_tape_all0 Dpos).
  1: repeat ctor.
  unfold InitES.
  f_equal.
  fext.
  destruct x; cbn.
  2,3: rewrite app_halftape_nil; unfold half_tape_cdr,half_tape_all0.
  all: reflexivity.
Qed.

Lemma set_ins_spec'{T}{T_enc:T->positive} {q st a q' st' flag}:
  is_inj T_enc ->
  set_ins T_enc (q, st) a = (q', st', flag) ->
    forall x,
    ((a = x) \/ set_in T_enc (q, st) x <->
     set_in T_enc (q', st') x) /\ 
    (((a = x) /\ ~ set_in T_enc (q, st) x \/ In x q) -> In x q').
Proof.
intros.
unfold set_ins in H0.
cbn in H0.
destruct (PositiveMap.find (T_enc a) st) eqn:E.
- invst H0.
  assert (a=x -> set_in T_enc (q',st') x). {
    intro. subst a.
    unfold set_in. cbn.
    destruct u. apply E.
  }
  split. 1: tauto.
  tauto.
- invst H0.
  clear H0.
  split.
  + unfold set_in.
    cbn.
    split; intro.
    * destruct H0 as [H0|H0].
      -- subst a. apply PositiveMap.gss.
      -- assert (a<>x) by cg.
         rewrite PositiveMap.gso; auto 1.
         intro H2.
         apply H1. symmetry. apply H,H2.
    * rewrite PositiveMapAdditionalFacts.gsspec in H0.
      destruct (PositiveMap.E.eq_dec (T_enc x) (T_enc a)) eqn:E0.
      -- left. symmetry. apply H,e.
      -- tauto.
  + intros.
    destruct H0 as [[H0a H0b]|H0].
    * subst a. cbn. tauto.
    * cbn. tauto.
Qed.

Section ClosedSetSearcher.

Hypothesis T:Type.
Hypothesis T_enc:T->positive.
Hypothesis T_enc_inj: is_inj T_enc.
Hypothesis In_T: (ExecState Σ)->T->Prop.
Hypothesis T_InitES:T.
Hypothesis In_T_InitES: In_T (InitES Σ Σ0) T_InitES.
Hypothesis T_step: (TM Σ)->T->option (list T).
Hypothesis T_step_spec:
  forall (tm : TM Σ) (x : T),
     match T_step tm x with
     | Some ls =>
         forall st0 : ExecState Σ,
         In_T st0 x ->
         exists (n : nat) (st1 : ExecState Σ) (x1 : T),
           Steps Σ tm (1 + n) st0 st1 /\ In_T st1 x1 /\ In x1 ls
     | None => True
     end.

Definition T_eqb t1 t2 := Pos.eqb (T_enc t1) (T_enc t2).
Lemma T_eqb_spec t1 t2:
  if T_eqb t1 t2 then t1=t2 else t1<>t2.
Proof.
  unfold T_eqb.
  destruct (Pos.eqb_spec (T_enc t1) (T_enc t2)); auto 2.
  cg.
Qed.

Fixpoint ins_all(q:list T)(st:PositiveMap.tree unit)(ls:list T) :=
  match ls with
  | nil => (q,st)
  | h::ls0 =>
    let (q',st') := fst (set_ins T_enc (q,st) h) in
    ins_all q' st' ls0
  end.

Fixpoint T_close_set_searcher(tm:TM Σ)(n:nat)(q:list T)(st:PositiveMap.tree unit):
  option (list T * PositiveMap.tree unit) :=
  match n with
  | O => Some (q,st)
  | S n0 =>
    match q with
    | nil => Some (q,st)
    | x::q0 =>
      match T_step tm x with
      | None => None
      | Some ls =>
        let (q',st') := ins_all q0 st ls in
        T_close_set_searcher tm n0 q' st'
      end
    end
  end.

Definition T_decider0(n:nat)(tm:TM Σ):bool :=
  let (q0,st0) := fst (set_ins T_enc (nil, PositiveMap.empty unit) T_InitES) in
  match T_close_set_searcher tm n q0 st0 with
  | Some (nil,q2') =>
    match PositiveMap.find (T_enc T_InitES) q2' with
    | Some _ => true
    | None => false
    end
  | _ => false
  end.

Definition T_decider(n:nat):HaltDecider :=
  fun tm => if T_decider0 n tm then Result_NonHalt else Result_Unknown.


Definition search_state_WF tm (qst:(list T * PositiveMap.tree unit)):=
  let (q,st):=qst in
  forall x,
  set_in T_enc qst x -> (In x q \/
    match T_step tm x with
    | None => False
    | Some ls => forall y, In y ls -> set_in T_enc qst y
    end).






Lemma ins_all_spec {q st ls q' st'}:
  (ins_all q st ls) = (q',st') ->
  ((forall x, ((In x ls \/ set_in T_enc (q,st) x)) <-> set_in T_enc (q',st') x) /\
   (forall x, ((In x ls /\ ~set_in T_enc (q,st) x \/ In x q) -> In x q'))).
Proof.
  gd st'. gd q'. gd st. gd q.
  induction ls.
  - intros.
    cbn in H.
    invst H. cbn.
    split; intros; cbn; tauto.
  - intros.
    cbn in H.
    destruct (set_ins T_enc (q, st) a) as [[q'0 st'0] flag] eqn:E.
    cbn in H.
    specialize (IHls _ _ _ _ H).
    pose proof (set_ins_spec' T_enc_inj E) as H0.
    destruct IHls as [I1 I2].
    split.
    + intros.
      specialize (I1 x).
      cbn. rewrite <-I1.
      specialize (H0 x). tauto.
    + cbn.
      intros.
      specialize (I2 x).
      specialize (H0 x).
      destruct H0 as [H0a H0b].
      destruct H1 as [H1|H1].
      * destruct H1 as [[H1|H1] H2].
        1: subst a; tauto.
        pose proof (T_eqb_spec a x).
        destruct (T_eqb a x).
        1: subst a; tauto.
        tauto.
      * tauto.
Qed.

Lemma set_in_dec {T0} (enc:T0->positive) s x:
  set_in enc s x \/
  ~ set_in enc s x.
Proof.
  unfold set_in.
  destruct (PositiveMap.find (enc x) (snd s)) as [[]|].
  - left. reflexivity.
  - right. cg.
Qed.


Lemma T_close_set_searcher_spec tm n q st:
  search_state_WF tm (q,st) ->
  match T_close_set_searcher tm n q st with
  | None => True
  | Some qst' =>
    search_state_WF tm qst'
  end.
Proof.
  gd st. gd q.
  induction n; intros.
  - unfold T_close_set_searcher.
    apply H.
  - unfold T_close_set_searcher.
    fold T_close_set_searcher.
    destruct q as [|h q0].
    1: apply H.
    epose proof (T_step_spec tm h) as H0.
    destruct (T_step tm h) eqn:E.
    2: trivial.
    destruct (ins_all q0 st l0) as [q' st'] eqn:E0.
    apply IHn.

    destruct (ins_all_spec E0) as [I1 I2].
    unfold search_state_WF in H.
    unfold search_state_WF.
    intros x H1.
    rewrite <-I1 in H1.
    destruct H1 as [H1|H1].
    + destruct ((set_in_dec T_enc (q0, st) x)) as [H2|H2].
      2: specialize (I2 x); tauto.
      specialize (H x H2). cbn in H.
      destruct H as [[H|H]|H].
      * subst x.
        right. rewrite E.
        intros y H3.
        rewrite <-I1.
        tauto.
      * left. apply I2. tauto.
      * right. destruct (T_step tm x) eqn:E1.
        2: tauto.
        intros y H3.
        rewrite <-I1.
        right. apply H,H3.
    + specialize (H x H1).
      destruct H as [[H|H]|H].
      * subst x.
        right. rewrite E.
        intros y H2.
        rewrite <-I1.
        tauto.
      * left. apply I2. tauto.
      * right. destruct (T_step tm x) eqn:E1.
        2: tauto.
        intros y H2.
        rewrite <-I1.
        right. apply H,H2.
Qed.


Definition in_search_state(st0:ExecState Σ)(S:(list T * PositiveMap.tree unit)) :=
  exists s0, set_in T_enc S s0 /\ In_T st0 s0.


Lemma T_decider0_spec n tm:
  T_decider0 n tm = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  intro.
  unfold T_decider0 in H.
  destruct (fst (set_ins T_enc (nil, PositiveMap.empty unit) T_InitES)) as [q0 st0] eqn:E0.
  epose proof (T_close_set_searcher_spec tm n q0 st0) as H0.
  destruct (T_close_set_searcher tm n q0 st0) as [[q1 st1]|].
  2: cg.
  destruct q1 as [|].
  2: cg.
  destruct (PositiveMap.find (T_enc T_InitES) st1) as [|] eqn:E2.
  2: cg.
  eassert (H1:_). {
    apply H0.
    cbn.
    intros.
    left.
    assert (set_WF T_enc (q0,st0)). {
      destruct (set_ins T_enc (nil, PositiveMap.empty unit) T_InitES) as [qst0 flag] eqn:E.
      eapply set_ins_spec.
      - apply T_enc_inj.
      - apply empty_set_WF.
      - rewrite E.
        cbn in E0. subst qst0.
        reflexivity.
    }
    unfold set_WF in H2.
    rewrite H2 in H1.
    apply H1.
  }
  clear H0. clear H.
  assert (X1:in_search_state (InitES Σ Σ0) (nil, st1)). {
    unfold in_search_state.
    exists T_InitES.
    split.
    2: apply In_T_InitES.
    unfold set_in.
    unfold snd. rewrite E2.
    f_equal.
    destruct u.
    reflexivity.
  }
  eapply CPS_correct.
  1: apply X1.
  unfold isClosed.
  intros.
  unfold in_search_state in H.
  destruct H as [s0 [Ha Hb]].
  cbn in H1.
  specialize (H1 _ Ha).
  destruct H1 as [H1|H1]. 1: contradiction.
  epose proof (T_step_spec tm s0) as H2.
  destruct (T_step tm s0) eqn:E1. 2: contradiction.
  specialize (H2 _ Hb).
  destruct H2 as [n1 [st3 [x1 [H2a [H2b H2c]]]]].
  exists n1. exists st3.
  repeat split; auto 1.
  unfold in_search_state.
  exists x1.
  split; auto 1.
  apply H1,H2c.
Qed.

Lemma T_decider_spec n BB:
  HaltDecider_WF BB (T_decider n).
Proof.
  unfold HaltDecider_WF.
  intros.
  unfold T_decider.
  epose proof (T_decider0_spec n tm).
  destruct (T_decider0 n tm); tauto.
Qed.

End ClosedSetSearcher.





Definition RepWL_ES_decider(n:nat):HaltDecider :=
  (T_decider _ RepWL_ES_enc RepWL_InitES RepWL_step n).

Lemma RepWL_ES_decider_spec n BB:
  HaltDecider_WF BB (RepWL_ES_decider n).
Proof.
  eapply T_decider_spec.
  - apply RepWL_ES_enc_inj.
  - apply In_RepWL_ES_InitES.
  - apply RepWL_step_spec.
Qed.

End MacroMachine_secion.







Section DFA_NFA_verifier.

Section dfa_nfa_decider.

Hypothesis U: Set.
Hypothesis U0: U.
Hypothesis U_enc: U->positive.
Hypothesis U_enc_inj: is_inj U_enc.
Hypothesis U_list:list U.
Hypothesis U_list_spec:
  forall s, In s U_list.
Hypothesis maxT:nat.
Hypothesis dfa: U->Σ->U.

Definition U_eqb(u1 u2:U) := Pos.eqb (U_enc u1) (U_enc u2).
Lemma U_eqb_spec:
  forall u1 u2, if U_eqb u1 u2 then u1=u2 else u1<>u2.
Proof.
  intros.
  unfold U_eqb.
  destruct ((U_enc u1 =? U_enc u2)%positive) eqn:E.
  - rewrite Pos.eqb_eq in E.
    apply U_enc_inj,E.
  - intro H. subst.
    rewrite Pos.eqb_refl in E.
    cg.
Qed.

Section genNFA.
Hypothesis tm:TM Σ.

Section verifyNFA.


Hypothesis nfa: (option (St*U))->Σ->(option (St*U))->bool.
Hypothesis nfa_acc: option (St*U) -> bool.



Section NFA_NonHalt.

Hypothesis nfa_h0:
  forall {i0},
  nfa None i0 None = true.

Hypothesis nfa_h:
  forall {s0 u0 i0},
  tm s0 i0 = None ->
  nfa (Some (s0,u0)) i0 None = true.

Hypothesis nfa_r:
  forall {s0 u0 i0 s1 i1},
  tm s0 i0 = Some {| nxt:= s1; out:=i1; dir:=Dpos |} ->
  nfa (Some (s0,u0)) i0 (Some (s1,dfa u0 i1)) = true.

Hypothesis nfa_l:
  forall {s0 i0 s1 u1 i1 i2 su2 su3},
  tm s0 i0 = Some {| nxt:= s1; out:=i1; dir:=Dneg |} ->
  nfa (Some (s1,u1)) i2 su2 = true ->
  nfa su2 i1 su3 = true ->
  nfa (Some (s0,dfa u1 i2)) i0 su3 = true.

Hypothesis dfa_0:
  dfa U0 Σ0 = U0.

Inductive NFA_match: (option (St*U))->Word->Prop :=
| NFA_match_O: NFA_match None nil
| NFA_match_S v0 v1 i w: nfa v0 i v1 = true -> NFA_match v1 w -> NFA_match v0 (i::w)
.

Definition makeES' (l0 r0:Word)(m0:Σ)(s0:St):ExecState Σ :=
  (s0,make_tape' half_tape_all0 l0 m0 r0 half_tape_all0).


Fixpoint DFA_match(w:Word):U :=
match w with
| nil => U0
| h::t => dfa (DFA_match t) h
end.

Definition ES_matched(l0 r0:Word)(m0:Σ)(s0:St):Prop :=
  exists n0,
  NFA_match (Some (s0,DFA_match l0)) ((m0::r0)++(repeat Σ0 n0)).


Lemma NFA_match_None w:
  NFA_match None w.
Proof.
  induction w.
  - ctor.
  - ector.
    + apply nfa_h0.
    + apply IHw.
Qed.


Lemma ES_matched_spec l0 r0 m0 s0:
  Halts _ tm (ListES_toES (Build_ListES l0 r0 m0 s0)) ->
  ES_matched l0 r0 m0 s0.
Proof.
  intros H.
  destruct H as [n H].
  gd H. gd s0. gd m0. gd r0. gd l0.
  induction n.
  - intros.
    destruct H as [st' [Ha Hb]].
    invst Ha. clear Ha.
    cbn in Hb.
    destruct (tm s0 m0) as [[s' d o]|] eqn:E. 1: cg.
    unfold ES_matched.
    eexists.
    cbn.
    ector.
    + apply nfa_h,E.
    + apply NFA_match_None.
  - intros.
    destruct H as [st' [Ha Hb]].
    replace (S n) with (n+1) in Ha by lia.
    destruct (Steps_split Ha) as [es' [H1a H1b]].
    invst H1a.
    invst H0. clear H0.
    epose proof (ListES_step_spec tm (Build_ListES l0 r0 m0 s0)) as H3.
    rewrite H2 in H3.
    destruct (ListES_step tm (Build_ListES l0 r0 m0 s0)) eqn:E. 2: cg.
    invst H3. clear H3.
    cbn in E.
    destruct (tm s0 m0) as [[s1 d o]|] eqn:E0. 2: cg.
    destruct d.
    + destruct l0 as [|m1 l0].
      1,2: invst E; clear E;
        eassert (X:_) by (
          apply IHn;
          esplit; split; eauto 1
        );
        unfold ES_matched;
        unfold ES_matched in X;
        destruct X as [n0 X];
        cbn in X;
        cbn;
        invst X;
        invst H4;
        epose proof (nfa_l E0 H3 H5) as A;
        try rewrite dfa_0 in A;
        exists n0;
        ector; eauto 1.
    + destruct r0 as [|m1 r0].
      1,2: invst E; clear E;
        eassert (X:_) by (
          apply IHn;
          esplit; split; eauto 1
        );
        unfold ES_matched;
        unfold ES_matched in X;
        destruct X as [n0 X];
        cbn in X;
        cbn.
      1: exists (S n0).
      2: exists (n0).
      1,2: ector; eauto 1;
        eapply nfa_r; eauto 1.
    Unshelve.
    exact 0.
Qed.

Lemma ES_not_matched_NonHalt:
  ~ES_matched nil nil Σ0 St0 ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  intros H H0.
  apply H.
  apply ES_matched_spec.
  rewrite ListES_toES_O.
  apply H0.
Qed.

Hypothesis nfa_acc_0: nfa_acc (Some (St0,U0)) = true.
Hypothesis nfa_acc_h: nfa_acc None = false.
Hypothesis nfa_acc_closed:
  forall {su0 su1},
  nfa su0 Σ0 su1 = true ->
  nfa_acc su0 = true ->
  nfa_acc su1 = true.

Lemma nfa_acc_spec:
  forall su0,
  nfa_acc su0 = true ->
  forall n, ~ NFA_match su0 (repeat Σ0 n).
Proof.
  intros.
  gd H. gd su0.
  induction n.
  - intros.
    cbn.
    intro H0.
    invst H0. cg.
  - intros.
    intro H0.
    cbn in H0.
    invst H0.
    apply (IHn v1 (nfa_acc_closed H4 H) H5).
Qed.

Lemma nfa_acc_closed_NonHalt:
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  apply ES_not_matched_NonHalt.
  unfold ES_matched.
  intro H.
  destruct H as [n0 H].
  cbn in H.
  replace (Σ0 :: repeat Σ0 n0) with (repeat Σ0 (S n0)) in H by reflexivity.
  eapply nfa_acc_spec; eauto 1.
Qed.

End NFA_NonHalt.







Definition StU_list :=
  concat (map (fun s => map (fun u => (s,u)) U_list) St_list).

Definition oStU_list :=
  None::(map Some StU_list).

Lemma StU_list_spec:
  forall s, In s StU_list.
Proof.
  intro s.
  unfold StU_list.
  rewrite in_concat.
  destruct s as [s0 s1].
  exists (map (fun u : U => (s0, u)) U_list).
  rewrite in_map_iff.
  repeat split.
  - exists s0.
    repeat split.
    apply St_list_spec.
  - rewrite in_map_iff.
    exists s1.
    repeat split.
    apply U_list_spec.
Qed.

Lemma oStU_list_spec:
  forall s, In s oStU_list.
Proof.
intro s.
destruct s as [s|].
- right.
  rewrite in_map_iff.
  exists s.
  repeat split.
  apply StU_list_spec.
- left. reflexivity.
Qed.

Definition forallb_U f :=
  forallb f U_list.

Definition forallb_oStU f :=
  forallb f oStU_list.



Lemma forallb_U_spec f:
  forallb_U f = true <-> forall s, f s = true.
Proof.
  unfold forallb_U.
  rewrite forallb_forall.
  split; intros.
  - apply H,U_list_spec.
  - apply H.
Qed.

Lemma forallb_oStU_spec f:
  forallb_oStU f = true <-> forall s, f s = true.
Proof.
  unfold forallb_oStU.
  rewrite forallb_forall.
  split; intros.
  - apply H,oStU_list_spec.
  - apply H.
Qed.

Definition nfa_h0_dec:bool :=
  forallb_Σ (fun i0 => nfa None i0 None).

Lemma nfa_h0_dec_spec:
  nfa_h0_dec = true ->
  forall i0,
  nfa None i0 None = true.
Proof.
  unfold nfa_h0_dec.
  rewrite forallb_Σ_spec.
  tauto.
Qed.

Definition nfa_h_dec:bool :=
  forallb_St (fun s0 =>
    forallb_U (fun u0 =>
      forallb_Σ (fun i0 =>
        match tm s0 i0 with
        | None => nfa (Some (s0,u0)) i0 None
        | _ => true
        end))).

Lemma nfa_h_dec_spec:
  nfa_h_dec = true ->
  forall s0 u0 i0,
  tm s0 i0 = None ->
  nfa (Some (s0,u0)) i0 None = true.
Proof.
  unfold nfa_h_dec.
  rewrite forallb_St_spec.
  intros.
  specialize (H s0).
  rewrite forallb_U_spec in H.
  specialize (H u0).
  rewrite forallb_Σ_spec in H.
  specialize (H i0).
  rewrite H0 in H.
  apply H.
Qed.

Definition nfa_r_dec:bool :=
  forallb_St (fun s0 =>
  forallb_U (fun u0 =>
  forallb_Σ (fun i0 =>
  match tm s0 i0 with
  | Some {| nxt:= s1; out:=i1; dir:=Dpos |} =>
    nfa (Some (s0,u0)) i0 (Some (s1,dfa u0 i1))
  | _ => true
  end))).

Lemma nfa_r_dec_spec:
  nfa_r_dec = true ->
  forall s0 u0 i0 s1 i1,
  tm s0 i0 = Some {| nxt:= s1; out:=i1; dir:=Dpos |} ->
  nfa (Some (s0,u0)) i0 (Some (s1,dfa u0 i1)) = true.
Proof.
  unfold nfa_r_dec.
  rewrite forallb_St_spec.
  intros.
  specialize (H s0).
  rewrite forallb_U_spec in H.
  specialize (H u0).
  rewrite forallb_Σ_spec in H.
  specialize (H i0).
  rewrite H0 in H.
  apply H.
Qed.

Definition nfa_l_dec:bool :=
  forallb_St (fun s0 =>
  forallb_Σ (fun i0 =>
  match tm s0 i0 with
  | Some {| nxt:= s1; out:=i1; dir:=Dneg |} =>
  forallb_U (fun u1 =>
  forallb_Σ (fun i2 =>
  forallb_oStU (fun su2 =>
  forallb_oStU (fun su3 =>
  if nfa (Some (s1,u1)) i2 su2 then
  if nfa su2 i1 su3 then nfa (Some (s0,dfa u1 i2)) i0 su3 else true else true
  ))))
  | _ => true
  end)).

Lemma nfa_l_dec_spec:
  nfa_l_dec = true ->
  forall s0 i0 s1 u1 i1 i2 su2 su3,
  tm s0 i0 = Some {| nxt:= s1; out:=i1; dir:=Dneg |} ->
  nfa (Some (s1,u1)) i2 su2 = true ->
  nfa su2 i1 su3 = true ->
  nfa (Some (s0,dfa u1 i2)) i0 su3 = true.
Proof.
  unfold nfa_l_dec.
  rewrite forallb_St_spec.
  intros.
  specialize (H s0).
  rewrite forallb_Σ_spec in H.
  specialize (H i0).
  rewrite H0 in H.
  rewrite forallb_U_spec in H.
  specialize (H u1).
  rewrite forallb_Σ_spec in H.
  specialize (H i2).
  rewrite forallb_oStU_spec in H.
  specialize (H su2).
  rewrite forallb_oStU_spec in H.
  specialize (H su3).
  rewrite H1 in H.
  rewrite H2 in H.
  apply H.
Qed.


Definition dfa_0_dec:=
  U_eqb (dfa U0 Σ0) U0.

Lemma dfa_0_dec_spec:
  dfa_0_dec = true ->
  dfa U0 Σ0 = U0.
Proof.
  unfold dfa_0_dec.
  intro H.
  pose proof (U_eqb_spec (dfa U0 Σ0) U0) as H0.
  rewrite H in H0.
  apply H0.
Qed.


Definition nfa_acc_0_dec:=
  nfa_acc (Some (St0,U0)).

Definition nfa_acc_h_dec:=
  negb (nfa_acc None).

Definition nfa_acc_closed_dec :=
  forallb_oStU (fun su0 =>
  forallb_oStU (fun su1 =>
  if nfa su0 Σ0 su1 then
  if nfa_acc su0 then nfa_acc su1 else true
  else true
  )).


Lemma nfa_acc_0_dec_spec:
  nfa_acc_0_dec = true ->
  nfa_acc (Some (St0,U0)) = true.
Proof.
  unfold nfa_acc_0_dec.
  tauto.
Qed.

Lemma nfa_acc_h_dec_spec:
  nfa_acc_h_dec = true ->
  nfa_acc None = false.
Proof.
  unfold nfa_acc_h_dec.
  unfold negb.
  destruct (nfa_acc None); cg.
Qed.

Lemma nfa_acc_closed_dec_spec:
  nfa_acc_closed_dec = true ->
  forall su0 su1,
  nfa su0 Σ0 su1 = true ->
  nfa_acc su0 = true ->
  nfa_acc su1 = true.
Proof.
  unfold nfa_acc_closed_dec.
  rewrite forallb_oStU_spec.
  intros.
  specialize (H su0).
  rewrite forallb_oStU_spec in H.
  specialize (H su1).
  rewrite H0 in H.
  rewrite H1 in H.
  apply H.
Qed.

Definition all_cond_dec :=
  nfa_h0_dec &&&
  nfa_h_dec &&&
  nfa_r_dec &&&
  nfa_l_dec &&&
  dfa_0_dec &&&
  nfa_acc_0_dec &&&
  nfa_acc_h_dec &&&
  nfa_acc_closed_dec.

Lemma shortcut_andb_spec(a b:bool):
  (a &&& b) = (a&&b)%bool.
Proof.
  destruct a,b; reflexivity.
Qed.

Lemma all_cond_dec_spec:
  all_cond_dec = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  intro H.
  unfold all_cond_dec in H.
  repeat rewrite shortcut_andb_spec in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [H0 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]].
  apply nfa_acc_closed_NonHalt.
  - apply nfa_h0_dec_spec,H0.
  - apply nfa_h_dec_spec,H1.
  - apply nfa_r_dec_spec,H2.
  - apply nfa_l_dec_spec,H3.
  - apply dfa_0_dec_spec,H4.
  - apply nfa_acc_0_dec_spec,H5.
  - apply nfa_acc_h_dec_spec,H6.
  - apply nfa_acc_closed_dec_spec,H7.
Qed.

End verifyNFA.




Definition pair_enc{T1 T2}(T1_enc:T1->positive)(T2_enc:T2->positive):(T1*T2)->positive :=
  fun x =>
  let (x1,x2):=x in
  enc_pair (T1_enc x1,T2_enc x2).

Lemma pair_enc_inj{T1 T2}(T1_enc:T1->positive)(T2_enc:T2->positive):
  is_inj T1_enc ->
  is_inj T2_enc ->
  is_inj (pair_enc T1_enc T2_enc).
Proof.
  intros H1 H2 x1 x2 H.
  unfold pair_enc in H.
  destruct x1,x2.
  pose proof (enc_pair_inj _ _ H).
  invst H0.
  f_equal; auto 2.
Qed.

Definition option_enc{T}(T_enc:T->positive):(option T)->positive :=
  fun x =>
  match x with
  | None => xH
  | Some x0 => (Pos.succ (T_enc x0))
  end.

Lemma option_enc_inj{T}(T_enc:T->positive):
  is_inj T_enc ->
  is_inj (option_enc T_enc).
Proof.
  intros H1 x1 x2 H.
  destruct x1,x2.
  - cbn in H.
    assert (T_enc t = T_enc t0) by lia.
    f_equal.
    auto 2.
  - cbn in H. lia.
  - cbn in H. lia.
  - reflexivity.
Qed.

Definition StU_enc: (St*U)->positive := pair_enc St_enc U_enc.

Lemma StU_enc_inj: is_inj StU_enc.
Proof.
  apply pair_enc_inj.
  - apply St_enc_inj.
  - apply U_enc_inj.
Qed.

Definition oStU := option (St*U).

Definition oStU_enc: oStU->positive := option_enc StU_enc.

Lemma oStU_enc_inj: is_inj oStU_enc.
Proof.
  apply option_enc_inj.
  apply StU_enc_inj.
Qed.

Definition nfa_entry := (oStU*Σ*oStU)%type.

Definition nfa_entry_enc := pair_enc (pair_enc oStU_enc Σ_enc) oStU_enc.

Lemma nfa_entry_enc_inj: is_inj nfa_entry_enc.
Proof.
  repeat apply pair_enc_inj.
  1,3: apply oStU_enc_inj.
  apply Σ_enc_inj.
Qed.

Definition nfa_t := PositiveMap.tree unit.

Definition nfa_ins(x:nfa_entry)(s:nfa_t):nfa_t :=
  PositiveMap.add (nfa_entry_enc x) tt s.

Definition nfa_at(x:nfa_entry)(s:nfa_t):bool :=
  match PositiveMap.find (nfa_entry_enc x) s with
  | Some _ => true
  | None => false
  end.
Definition nfa_ins'(x:nfa_entry)(s:nfa_t*bool):(nfa_t*bool) :=
  let (s0,flag):=s in
  (nfa_ins x s0,flag&&&nfa_at x s0).


Fixpoint for_loop{T}{S}(f:S->T->S)(ls:list T)(s:S):S :=
  match ls with
  | nil => s
  | h::t => for_loop f t (f s h)
  end.

Definition for_Dir{S} f:S->S := for_loop f Dir_list.
Definition for_Σ{S} f:S->S := for_loop f Σ_list.
Definition for_St{S} f:S->S := for_loop f St_list.
Definition for_U{S} f:S->S := for_loop f U_list.
Definition for_oStU{S} f:S->S := for_loop f oStU_list.


Definition nfa_h0_rec:nfa_t->nfa_t :=
  for_Σ (fun (s:nfa_t) i0 => nfa_ins ((None,i0,None)) s).

Definition nfa_h_rec:nfa_t->nfa_t :=
  for_St (fun s s0 =>
  for_U (fun s u0 =>
  for_Σ (fun s i0 =>
  match tm s0 i0 with
  | None => nfa_ins ((Some (s0,u0),i0,None)) s
  | _ => s
  end
  ) s) s).

Definition nfa_r_rec:nfa_t->nfa_t :=
  for_St (fun s s0 =>
  for_Σ (fun s i0 =>
  match tm s0 i0 with
  | Some {| nxt:= s1; out:=i1; dir:=Dpos |} =>
    for_U (fun s u0 => nfa_ins ((Some (s0,u0)),i0,(Some (s1,dfa u0 i1))) s) s
  | _ => s
  end) s).

Definition nfa_l_rec:(nfa_t*bool)->(nfa_t*bool) :=
  for_St (fun s s0 =>
  for_Σ (fun s i0 =>
  match tm s0 i0 with
  | Some {| nxt:= s1; out:=i1; dir:=Dneg |} =>
    for_U (fun s u1 =>
    for_Σ (fun s i2 =>
    for_oStU (fun (s:nfa_t*bool) su2 =>
    let (nfa,flag):=s in
    if nfa_at (Some (s1,u1),i2,su2) nfa then
      for_oStU (fun (s:nfa_t*bool) su3 =>
      let (nfa,flag):=s in
      if nfa_at (su2,i1,su3) nfa then
      nfa_ins' ((Some (s0,dfa u1 i2)),i0,su3) s
      else s
      ) s
    else s
    ) s) s) s
  | _ => s
  end) s).


Fixpoint do_until0{T}(f:T->(T*bool))(n:nat)(x:T):T :=
match n with
| O => x
| S n0 =>
  let (x',flag):=(f x) in
  if flag then x' else (do_until0 f n0 x')
end.


Definition do_until{T}(f:T->(T*bool)):T->T :=
  do_until0 f maxT.


Definition nfa_rec:nfa_t :=
  do_until (fun s => nfa_l_rec (s,true)) (nfa_r_rec (nfa_h_rec (nfa_h0_rec (PositiveMap.empty _)))).


Definition nfa_acc_t := PositiveMap.tree unit.
Definition nfa_acc_ins(x:oStU)(s:nfa_acc_t):nfa_acc_t := PositiveMap.add (oStU_enc x) tt s.
Definition nfa_acc_at(x:oStU)(s:nfa_acc_t):bool := 
match PositiveMap.find (oStU_enc x) s with
| Some _ => true
| None => false
end.
Definition nfa_acc_ins'(x:oStU)(s:nfa_acc_t*bool):(nfa_acc_t*bool) :=
  let (s0,flag):=s in
  (nfa_acc_ins x s0,flag&&&nfa_acc_at x s0).

Definition nfa_acc_0_rec:nfa_acc_t->nfa_acc_t :=
  nfa_acc_ins (Some (St0,U0)).

Definition nfa_acc_closed_rec(nfa:nfa_t):((nfa_acc_t*bool))->((nfa_acc_t*bool)) :=
  for_oStU (fun s su0 =>
  for_oStU (fun (s:(nfa_acc_t*bool)) su1 =>
  let (nfa_acc,flag):=s in
  if nfa_at (su0,Σ0,su1) nfa then
  if nfa_acc_at su0 nfa_acc then (nfa_acc_ins' su1 (nfa_acc,flag)) else s
  else s) s).


Definition nfa_acc_rec(nfa:nfa_t):nfa_acc_t :=
  do_until (fun s => nfa_acc_closed_rec nfa (s,true)) (nfa_acc_0_rec (PositiveMap.empty _)).


Definition dfa_nfa_decider :=
  let nfa := nfa_rec in
  let nfa_acc := nfa_acc_rec nfa in
  if all_cond_dec (fun x1 x2 x3 => nfa_at (x1,x2,x3) nfa) (fun x => nfa_acc_at x nfa_acc) then Result_NonHalt
  else Result_Unknown.
End genNFA.



Lemma dfa_nfa_decider_spec:
  HaltDecider_WF (N.to_nat BB) dfa_nfa_decider.
Proof.
  unfold HaltDecider_WF.
  intro tm.
  destruct (dfa_nfa_decider tm) eqn:E.
  - unfold dfa_nfa_decider in E.
    destruct (all_cond_dec tm); cg.
  - unfold dfa_nfa_decider in E.
    destruct (all_cond_dec tm) eqn:E0; cg.
    eapply all_cond_dec_spec.
    apply E0.
  - trivial.
Qed.

Section WDFA.

Hypothesis wdfa:U->Σ->(U*Z).

Fixpoint WDFA_match(ls:Word):U*Z :=
match ls with
| nil => (U0,Z0)
| h::t => let (u,z) := WDFA_match t in
  let (u',a) := wdfa u h in
  (u',(z+a)%Z)
end.

Definition WDFA_pop(u0:U) :=
  concat
  (map (fun i0 =>
  map (fun u1 => (u1,i0,snd (wdfa u1 i0))) (filter (fun u1 => U_eqb (fst (wdfa u1 i0)) u0) U_list))
  Σ_list).

Lemma WDFA_pop_spec u0:
  forall u1 i0 d1,
  wdfa u1 i0 = (u0,d1) ->
  In (u1,i0,d1) (WDFA_pop u0).
Proof.
  intros.
  unfold WDFA_pop.
  rewrite in_concat.
  eexists.
  split.
  - rewrite in_map_iff.
    exists i0.
    split.
    2: apply Σ_list_spec.
    reflexivity.
  - rewrite in_map_iff.
    exists u1.
    split.
    + rewrite H.
      reflexivity.
    + rewrite filter_In.
      split.
      1: apply U_list_spec.
      rewrite H.
      cbn.
      pose proof (U_eqb_spec u0 u0).
      destruct (U_eqb u0 u0); cg.
Qed.

Definition wdfa_0:=
  wdfa U0 Σ0 = (U0,Z0).

Definition wdfa_0_dec :=
  let (u0,z0):=wdfa U0 Σ0 in
  U_eqb u0 U0 &&&
  Z.eqb z0 Z0.

Lemma wdfa_0_dec_spec:
  wdfa_0_dec = true ->
  wdfa_0.
Proof.
  unfold wdfa_0_dec,wdfa_0.
  destruct (wdfa U0 Σ0).
  intro H.
  rewrite shortcut_andb_spec in H.
  rewrite Bool.andb_true_iff in H.
  destruct H as [H H0].
  f_equal.
  - pose proof (U_eqb_spec u U0).
    rewrite H in H1.
    apply H1.
  - lia.
Qed.

Section WDFA_sgn.

Hypothesis wdfa_sgn: Dir->U->bool.
Definition wdfa_sgn_closed:=
  forall d0 u0,
  wdfa_sgn d0 u0 = true ->
  forall u1 i0 d1,
  wdfa u1 i0 = (u0,d1) ->
  ((d1*(Dir_to_Z d0)>=0)%Z /\
   wdfa_sgn d0 u1 = true).

Lemma wdfa_sgn_spec:
  wdfa_sgn_closed ->
  forall ls u0 d1,
  WDFA_match ls = (u0,d1) ->
  forall d0,
  wdfa_sgn d0 u0 = true ->
  (d1*(Dir_to_Z d0)>=0)%Z.
Proof.
  unfold wdfa_sgn_closed.
  intros H0 ls.
  induction ls.
  - cbn; intros.
    invst H. clear H.
    cbn. lia.
  - cbn; intros.
    destruct (WDFA_match ls) as (u0',d1') eqn:E.
    specialize (IHls _ _ eq_refl).
    destruct (wdfa u0' a) as (u',a') eqn:E0.
    invst H. clear H.
    specialize (H0 _ _ H1 _ _ _ E0).
    destruct H0 as [H0a H0b].
    specialize (IHls _ H0b).
    destruct d0; cbn; cbn in IHls,H0a; lia.
Qed.

Definition wdfa_sgn_closed_dec :=
  forallb_Dir (fun d0 =>
  forallb_U (fun u0 =>
  if wdfa_sgn d0 u0 then
  forallb_U (fun u1 =>
  forallb_Σ (fun i0 =>
  let (u0',d1) := wdfa u1 i0 in
  if U_eqb u0' u0 then
  (d1*(Dir_to_Z d0) >=? 0)%Z &&&
  wdfa_sgn d0 u1
  else true))
  else true)).

Lemma wdfa_sgn_closed_dec_spec :
  wdfa_sgn_closed_dec = true ->
  wdfa_sgn_closed.
Proof.
  unfold wdfa_sgn_closed_dec.
  unfold wdfa_sgn_closed.
  rewrite forallb_Dir_spec.
  intros.
  specialize (H d0).
  rewrite forallb_U_spec in H.
  specialize (H u0).
  rewrite H0 in H.
  rewrite forallb_U_spec in H.
  specialize (H u1).
  rewrite forallb_Σ_spec in H.
  specialize (H i0).
  rewrite H1 in H.
  pose proof (U_eqb_spec u0 u0).
  destruct (U_eqb u0 u0). 2: cg.
  rewrite shortcut_andb_spec in H.
  rewrite Bool.andb_true_iff in H.
  split.
  2: apply H.
  lia.
Qed.

End WDFA_sgn.


Definition wdfa_sgn_t := PositiveMap.tree unit.

Definition wdfa_sgn_ins(x:U)(s:wdfa_sgn_t):wdfa_sgn_t :=
  PositiveMap.add (U_enc x) tt s.

Definition wdfa_sgn_at(x:U)(s:wdfa_sgn_t):bool :=
  match PositiveMap.find (U_enc x) s with
  | Some _ => true
  | None => false
  end.
Definition wdfa_sgn_ins'(x:U)(s:wdfa_sgn_t*bool):(wdfa_sgn_t*bool) :=
  let (s0,flag):=s in
  (wdfa_sgn_ins x s0,flag&&&wdfa_sgn_at x s0).

Definition wdfa_sgn_rec0(d0:Dir) :=
  for_U (fun s u0 =>
  for_Σ (fun s i0 =>
  let (u1,d1):=wdfa u0 i0 in
  if (d1*(Dir_to_Z d0)>=?0)%Z &&& (negb (wdfa_sgn_at u0 (fst s))) then s
  else wdfa_sgn_ins' u1 s) s).

Definition wdfa_sgn_rec1(d0:Dir) :=
  do_until (fun s => wdfa_sgn_rec0 d0 (s,true)) (PositiveMap.empty _).

Definition wdfa_sgn_rec: Dir->U->bool :=
  let spos := wdfa_sgn_rec1 Dpos in
  let sneg := wdfa_sgn_rec1 Dneg in
  fun d0 =>
  match d0 with
  | Dpos => fun u0 => negb (wdfa_sgn_at u0 spos)
  | Dneg => fun u0 => negb (wdfa_sgn_at u0 sneg)
  end.

End WDFA.

End dfa_nfa_decider.

Inductive nat_n:nat->Set :=
| nat_n_O n: nat_n n
| nat_n_S n: nat_n n -> nat_n (S n)
.


Fixpoint nat_n_list(n:nat):list (nat_n n).
  destruct n as [|n0].
  - apply ((nat_n_O O)::nil).
  - apply ((nat_n_O (S n0))::(map (fun x => nat_n_S n0 x) (nat_n_list n0))).
Defined.



Lemma nat_n_list_spec n:
  forall s, In s (nat_n_list n).
Proof.
  induction n as [|n].
  - intros.
    left.
    remember 0 as c0.
    destruct s0; subst; auto 1; cg.
  - intros.
    remember (S n) as Sn.
    destruct s0.
    + subst.
      left. reflexivity.
    + right.
      rewrite in_map_iff.
      exists s0.
      repeat split.
      invst HeqSn.
      apply IHn.
Qed.




Fixpoint nat_n_to_nat(n:nat)(x:nat_n n):nat.
  destruct x as [|x0].
  - apply O.
  - apply (S (nat_n_to_nat x0 x)).
Defined.

Fixpoint nat_n_from_nat(n:nat)(x:nat):nat_n n.
  destruct x as [|x0].
  - apply nat_n_O.
  - destruct n as [|n0].
    + apply nat_n_O.
    + apply nat_n_S.
      apply (nat_n_from_nat n0 x0).
Defined.

Lemma nat_n_from_to_nat(n:nat)(x:nat_n n):
  nat_n_from_nat n (nat_n_to_nat n x) = x.
Proof.
  gd x.
  induction n.
  - intros.
    remember 0 as c0.
    destruct x; subst; cbn; cg.
  - intros.
    remember (S n) as Sn.
    destruct x.
    1: subst; reflexivity.
    invst HeqSn.
    cbn.
    f_equal.
    apply IHn.
Qed.


Lemma nat_n_to_nat_inj n: is_inj (nat_n_to_nat n).
Proof.
  unfold is_inj.
  intros.
  pose proof (nat_n_from_to_nat n a) as Ha.
  pose proof (nat_n_from_to_nat n b) as Hb.
  rewrite H in Ha.
  cg.
Qed.

Definition nat_n_enc(n:nat)(x:nat_n n):positive := Pos.of_succ_nat (nat_n_to_nat n x).

Lemma nat_n_enc_inj n: is_inj (nat_n_enc n).
Proof.
  intros x1 x2 H.
  unfold nat_n_enc in H.
  apply nat_n_to_nat_inj.
  lia.
Qed.



Definition make_dfa(f:nat->Σ->nat)(n:nat)(u:nat_n n)(i:Σ) :=
  nat_n_from_nat n (f (nat_n_to_nat _ u) i).

Definition dfa_nfa_verifier(n:nat)(f:nat->Σ->nat):HaltDecider :=
fun tm => (dfa_nfa_decider (nat_n n) (nat_n_O n) (nat_n_enc n) (nat_n_list n) 1000000 (make_dfa f n) tm).

Lemma dfa_nfa_verifier_spec n f:
  HaltDecider_WF (N.to_nat BB) (dfa_nfa_verifier n f).
Proof.
  unfold dfa_nfa_verifier.
  apply dfa_nfa_decider_spec.
  - apply nat_n_enc_inj.
  - apply nat_n_list_spec.
Qed.


End DFA_NFA_verifier.


Section MITMWFAR.

Section MITMWFAR_0.

Hypothesis n_l:nat.
Hypothesis n_r:nat.
Definition U_l := nat_n n_l.
Definition U_r := nat_n n_r.
Definition U0_l := nat_n_O n_l.
Definition U0_r := nat_n_O n_r.

Definition U_l_enc := nat_n_enc n_l.
Definition U_r_enc := nat_n_enc n_r.
Definition U_l_enc_inj := nat_n_enc_inj n_l.
Definition U_r_enc_inj := nat_n_enc_inj n_r.

Definition U_l_list := nat_n_list n_l.
Definition U_r_list := nat_n_list n_r.


Hypothesis wdfa_l:U_l->Σ->(U_l*Z).
Hypothesis wdfa_r:U_r->Σ->(U_r*Z).

Hypothesis wdfa_l_0: wdfa_0 U_l U0_l wdfa_l.
Hypothesis wdfa_r_0: wdfa_0 U_r U0_r wdfa_r.

Hypothesis wdfa_sgn_l:Dir->U_l->bool.
Hypothesis wdfa_sgn_r:Dir->U_r->bool.

Hypothesis wdfa_sgn_l_closed: wdfa_sgn_closed U_l wdfa_l wdfa_sgn_l.
Hypothesis wdfa_sgn_r_closed: wdfa_sgn_closed U_r wdfa_r wdfa_sgn_r.

Definition wdfa_sgn_l_spec := wdfa_sgn_spec U_l U0_l wdfa_l wdfa_sgn_l wdfa_sgn_l_closed.
Definition wdfa_sgn_r_spec := wdfa_sgn_spec U_r U0_r wdfa_r wdfa_sgn_r wdfa_sgn_r_closed.

Definition Z_enc(x:Z):positive :=
match x with
| Z0 => xH
| Zpos x0 => xI x0
| Zneg x0 => xO x0
end.

Lemma Z_enc_inj: is_inj Z_enc.
Proof.
  intros x1 x2 H.
  unfold Z_enc in H.
  destruct x1,x2; cg.
Qed.

Definition oDir_to_Z(x:option Dir) :=
match x with
| None => Z0
| Some x0 => Dir_to_Z x0
end.

Definition MITM_WDFA_ES := (U_l*U_r*Σ*St*Z*(option Dir))%type.

Definition MITM_WDFA_ES_enc:MITM_WDFA_ES->positive :=
  (pair_enc (pair_enc (pair_enc (pair_enc (pair_enc U_l_enc U_r_enc) Σ_enc) St_enc) Z_enc) (option_enc Dir_enc)).
Lemma MITM_WDFA_ES_enc_inj: is_inj MITM_WDFA_ES_enc.
Proof.
  unfold MITM_WDFA_ES_enc.
  repeat apply pair_enc_inj.
  - apply U_l_enc_inj.
  - apply U_r_enc_inj.
  - apply Σ_enc_inj.
  - apply St_enc_inj.
  - apply Z_enc_inj.
  - apply option_enc_inj,Dir_enc_inj.
Qed.


Definition In_MITM_WDFA_ES(es:ExecState Σ)(es1:MITM_WDFA_ES):Prop :=
  exists es0:ListES,
  es = ListES_toES es0 /\
  let (l0,r0,m0,s0):=es0 in
  let '(l1,r1,m1,s1,d1,g1):=es1 in
  exists (dl:Z) (dr:Z) (c1:N),
  (d1+(oDir_to_Z g1)*(Z.of_N c1) = dl+dr)%Z /\
  WDFA_match U_l U0_l wdfa_l l0 = (l1,dl) /\
  WDFA_match U_r U0_r wdfa_r r0 = (r1,dr) /\
  m0 = m1 /\
  s0 = s1.

Definition MITM_WDFA_InitES:MITM_WDFA_ES :=
  (U0_l,U0_r,Σ0,St0,Z0,None).

Lemma In_MITM_WDFA_InitES:
  In_MITM_WDFA_ES (InitES Σ Σ0) MITM_WDFA_InitES.
Proof.
  eexists.
  split.
  1: symmetry; apply ListES_toES_O.
  cbn.
  exists Z0. exists Z0. exists N0.
  repeat split.
Qed.

Lemma shortcut_orb_spec:
  forall a b : bool, (a ||| b) = (a || b)%bool.
Proof.
  intros a b.
  destruct a,b; reflexivity.
Qed.

Definition MITM_WDFA_ES_good(es:MITM_WDFA_ES):bool :=
  let '(l1,r1,m1,s1,d1,g1):=es in
  negb (
  ((d1>?0 &&& (oDir_to_Z g1)>=?0)%Z&&&(wdfa_sgn_l Dneg l1)&&&(wdfa_sgn_r Dneg r1)) |||
  ((d1<?0 &&& (oDir_to_Z g1)<=?0)%Z&&&(wdfa_sgn_l Dpos l1)&&&(wdfa_sgn_r Dpos r1))).

Lemma MITM_WDFA_ES_good_spec es es0:
  In_MITM_WDFA_ES es0 es ->
  MITM_WDFA_ES_good es = true.
Proof.
  unfold In_MITM_WDFA_ES,MITM_WDFA_ES_good.
  destruct es as [[[[[l1 r1] m1] s1] d1] g1].
  repeat rewrite shortcut_andb_spec.
  repeat rewrite shortcut_orb_spec.
  intro H.
  destruct H as [es1 [Ha Hb]].
  destruct es1 as [l0 r0 m0 s0].
  destruct Hb as [dl [dr [c1 [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]]]]].
  subst.
  rewrite Bool.negb_true_iff.
  rewrite Bool.orb_false_iff.
  repeat rewrite Bool.andb_false_iff.
  split.
  - destruct ((d1 >? 0)%Z) eqn:E. 2: tauto.
    destruct (oDir_to_Z g1 >=? 0)%Z eqn:E0. 2: tauto.
    right.
    destruct (wdfa_sgn_l Dneg l1) eqn:E1; cbn. 2: tauto.
    destruct (wdfa_sgn_r Dneg r1) eqn:E2; cbn. 2: tauto.
    pose proof (wdfa_sgn_l_spec _ _ _ Hb2 _ E1) as X1.
    pose proof (wdfa_sgn_r_spec _ _ _ Hb3 _ E2) as X2.
    cbn in X1,X2.
    lia.
  - destruct ((d1 <? 0)%Z) eqn:E. 2: tauto.
    destruct (oDir_to_Z g1 <=? 0)%Z eqn:E0. 2: tauto.
    right.
    destruct (wdfa_sgn_l Dpos l1) eqn:E1; cbn. 2: tauto.
    destruct (wdfa_sgn_r Dpos r1) eqn:E2; cbn. 2: tauto.
    pose proof (wdfa_sgn_l_spec _ _ _ Hb2 _ E1) as X1.
    pose proof (wdfa_sgn_r_spec _ _ _ Hb3 _ E2) as X2.
    cbn in X1,X2.
    lia.
Qed.

Lemma MITM_WDFA_ES_generalize_1 {es0 l1 r1 m1 s1 d1 g}:
  In_MITM_WDFA_ES es0 (l1,r1,m1,s1,d1,None) ->
  In_MITM_WDFA_ES es0 (l1,r1,m1,s1,d1,Some g).
Proof.
  unfold In_MITM_WDFA_ES.
  intro H.
  destruct H as [es1 [Ha Hb]].
  exists es1.
  split; auto 1.
  destruct es1 as [l0 r0 m0 s0].
  destruct Hb as [dl [dr [c1 [Hb Hc]]]].
  exists dl. exists dr. exists N0.
  cbn in Hb.
  cbn.
  rewrite Z.mul_0_r.
  tauto.
Qed.

Lemma MITM_WDFA_ES_generalize_2 {es0 l1 r1 m1 s1 d1 g}:
  In_MITM_WDFA_ES es0 (l1,r1,m1,s1,d1,Some g) ->
  In_MITM_WDFA_ES es0 (l1,r1,m1,s1,(d1-(oDir_to_Z (Some g)))%Z,Some g).
Proof.
  unfold In_MITM_WDFA_ES.
  intro H.
  destruct H as [es1 [Ha Hb]].
  exists es1.
  split; auto 1.
  destruct es1 as [l0 r0 m0 s0].
  destruct Hb as [dl [dr [c1 [Hb Hc]]]].
  exists dl. exists dr. exists (c1+1)%N.
  cbn in Hb.
  cbn.
  repeat split; try tauto.
  lia.
Qed.

Lemma MITM_WDFA_ES_split {es0 l1 r1 m1 s1 d1 g}:
  In_MITM_WDFA_ES es0 (l1,r1,m1,s1,d1,Some g) ->
  (In_MITM_WDFA_ES es0 (l1,r1,m1,s1,d1,None) \/
   In_MITM_WDFA_ES es0 (l1,r1,m1,s1,(d1+(oDir_to_Z (Some g)))%Z,Some g)).
Proof.
  unfold In_MITM_WDFA_ES.
  intro H.
  destruct H as [es1 [Ha Hb]].
  destruct es1 as [l0 r0 m0 s0].
  destruct Hb as [dl [dr [c1 [Hb Hc]]]].
  destruct c1 as [|c1].
  - left.
    eexists.
    split.
    1: apply Ha.
    cbn.
    exists dl. exists dr. exists N0.
    cbn in Hb.
    rewrite Z.mul_0_r in Hb.
    tauto.
  - right.
    eexists.
    split.
    1: apply Ha.
    cbn.
    exists dl. exists dr.
    exists ((Npos c1)-1)%N.
    cbn in Hb.
    split. 2: tauto.
    destruct g; unfold Dir_to_Z; unfold Dir_to_Z in Hb; lia.
Qed.

Hypothesis max_d:Z.

Definition MITM_WDFA_ES_simplify(es:MITM_WDFA_ES):list MITM_WDFA_ES :=
let '(l1,r1,m1,s1,d1,g):=es in
match g with
| None =>
  if ((Z.abs d1) >=? max_d)%Z then
    match d1 with
    | Zpos _ => (l1,r1,m1,s1,d1,Some Dpos)::nil
    | Zneg _ => (l1,r1,m1,s1,d1,Some Dneg)::nil
    | Z0 => es::nil
    end
  else es::nil
| Some g0 =>
  match ((Z.abs d1) - max_d)%Z with
  | Zpos _ => (l1,r1,m1,s1,(d1-(oDir_to_Z g))%Z,g)::nil
  | Zneg _ => (l1,r1,m1,s1,d1,None)::(l1,r1,m1,s1,(d1+(oDir_to_Z g))%Z,g)::nil
  | Z0 => es::nil
  end
end.

Lemma MITM_WDFA_ES_simplify_spec {es es0}:
  In_MITM_WDFA_ES es0 es ->
  exists es', In_MITM_WDFA_ES es0 es' /\ In es' (MITM_WDFA_ES_simplify es).
Proof.
  unfold MITM_WDFA_ES_simplify.
  destruct es as [[[[[l1 r1] m1] s1] d1] g1].
  destruct g1 as [g1|].
  - destruct ((Z.abs d1 - max_d)%Z).
    + intro H.
      eexists.
      split. 1: apply H.
      left. reflexivity.
    + intro H.
      eexists.
      split. 2: left; reflexivity.
      apply MITM_WDFA_ES_generalize_2,H.
    + intro H.
      destruct (MITM_WDFA_ES_split H) as [H0|H0].
      * eexists.
        split. 2: left; reflexivity.
        auto 1.
      * eexists.
        split. 2: right; left; reflexivity.
        auto 1.
  - destruct ((Z.abs d1 >=? max_d)%Z).
    + destruct d1.
      * intro H.
        eexists.
        split. 2: left; reflexivity.
        auto 1.
      * intro H.
        eexists.
        split. 2: left; reflexivity.
        apply MITM_WDFA_ES_generalize_1,H.
      * intro H.
        eexists.
        split. 2: left; reflexivity.
        apply MITM_WDFA_ES_generalize_1,H.
    + intro H.
      eexists.
      split. 2: left; reflexivity.
      auto 1.
Qed.

Definition MITM_WDFA_ES_filter(ls:list MITM_WDFA_ES):list MITM_WDFA_ES :=
  concat (map MITM_WDFA_ES_simplify (filter MITM_WDFA_ES_good ls)).


Lemma MITM_WDFA_ES_filter_spec es es0 ls:
  In_MITM_WDFA_ES es0 es ->
  In es ls ->
  exists es', In_MITM_WDFA_ES es0 es' /\ In es' (MITM_WDFA_ES_filter ls).
Proof.
  intros H H0.
  unfold MITM_WDFA_ES_filter.
  destruct (MITM_WDFA_ES_simplify_spec H) as [es' [H1 H2]].
  exists es'.
  split; auto 1.
  rewrite in_concat.
  eexists.
  split. 2: apply H2.
  rewrite in_map_iff.
  eexists.
  split. 1: reflexivity.
  rewrite filter_In.
  split. 1: auto 1.
  eapply MITM_WDFA_ES_good_spec,H.
Qed.



Definition pop_l := (WDFA_pop U_l U_l_enc U_l_list wdfa_l).
Definition pop_r := (WDFA_pop U_r U_r_enc U_r_list wdfa_r).

Definition MITM_WDFA_ES_step(tm:TM Σ)(es:MITM_WDFA_ES):option (list MITM_WDFA_ES) :=
let '(l1,r1,m1,s1,d1,g1):=es in
match tm s1 m1 with
| None => None
| Some {| nxt:=s2; dir:=d2; out:=m2 |} =>
  Some
  match d2 with
  | Dpos =>
    let (l1',dl):=wdfa_l l1 m2 in
    MITM_WDFA_ES_filter
    (map (fun x => let '(r1',m3,dr):=x in (l1',r1',m3,s2,(d1+dl-dr)%Z,g1)) (pop_r r1))
  | Dneg =>
    let (r1',dr):=wdfa_r r1 m2 in
    MITM_WDFA_ES_filter
    (map (fun x => let '(l1',m3,dl):=x in (l1',r1',m3,s2,(d1+dr-dl)%Z,g1)) (pop_l l1))
  end
end.


Lemma MITM_WDFA_ES_step_spec0 tm x:
  match MITM_WDFA_ES_step tm x with
  | Some ls =>
      forall st0,
      In_MITM_WDFA_ES st0 x ->
      exists n st1,
        Steps Σ tm (1 + n) st0 st1 /\ exists x1, In_MITM_WDFA_ES st1 x1 /\ In x1 ls
  | None => True
  end.
Proof.
  unfold MITM_WDFA_ES_step.
  destruct x as [[[[[l1 r1] m1] s1] d1] g1].
  destruct (tm s1 m1) as [[s2 d2 m2]|] eqn:E.
  2: trivial.
  intros st0 H.
  exists 0.
  unfold In_MITM_WDFA_ES in H.
  destruct H as [[l0 r0 m0 s0] [Ha [dl [dr [c1 [Hb [Hc [Hd [He Hf]]]]]]]]].
  subst.
  remember (ListES_step tm (Build_ListES l0 r0 m1 s1)) as st1.
  pose proof Heqst1 as Heqst1'.
  cbn in Heqst1.
  rewrite E in Heqst1.
  destruct st1 as [st1|]. 2: cg.
  injection Heqst1. clear Heqst1. intro Heqst1.
  exists (ListES_toES st1).
  destruct d2.
  {
    destruct l0 as [|m4 l0].
    - cbn in Hc.
      invst Hc. clear Hc.
      destruct (wdfa_r r1 m2) as [u' a0] eqn:E2.
      split.
      {
        ector. 1: ector.
        rewrite ListES_step_spec,<-Heqst1'.
        reflexivity.
      }
      eapply MITM_WDFA_ES_filter_spec with (es:=(_,_,_,_,_,_)).
      + unfold In_MITM_WDFA_ES.
        eexists.
        split.
        1: reflexivity.
        cbn.
        rewrite Hd,E2.
        exists Z0. exists (dr + a0)%Z. exists c1.
        repeat split.
        assert (A:((d1+a0) + oDir_to_Z g1 * Z.of_N c1)%Z = (0 + (dr+a0))%Z) by lia.
        apply A.
      + rewrite in_map_iff.
        eexists (_,_,Z0).
        split.
        -- rewrite Z.sub_0_r. reflexivity.
        -- unfold pop_l.
           apply WDFA_pop_spec; auto 1.
           ++ apply U_l_enc_inj.
           ++ apply nat_n_list_spec.
    - subst st1.
      cbn in Hc.
      destruct (WDFA_match U_l U0_l wdfa_l l0) as [l1' dl'] eqn:E0.
      destruct (wdfa_l l1' m4) as [u' a] eqn:E1.
      inversion Hc. subst u'. subst dl. clear Hc.
      destruct (wdfa_r r1 m2) as [u' a0] eqn:E2.
      split.
      {
        ector. 1: ector.
        rewrite ListES_step_spec,<-Heqst1'.
        reflexivity.
      }
      eapply MITM_WDFA_ES_filter_spec with (es:=(_,_,_,_,_,_)).
      + unfold In_MITM_WDFA_ES.
        eexists.
        split.
        1: reflexivity.
        cbn.
        rewrite E0,Hd,E2.
        exists dl'. exists (dr + a0)%Z. exists c1.
        repeat split.
        assert (A:((d1+a0-a) + oDir_to_Z g1 * Z.of_N c1)%Z = (dl' + (dr+a0))%Z) by lia.
        apply A.
      + rewrite in_map_iff.
        eexists (_,_,a).
        split.
        -- reflexivity.
        -- unfold pop_l.
           apply WDFA_pop_spec; auto 1.
           ++ apply U_l_enc_inj.
           ++ apply nat_n_list_spec.
  }
  {
    destruct r0 as [|m4 r0].
    - cbn in Hd.
      invst Hd. clear Hd.
      destruct (wdfa_l l1 m2) as [u' a0] eqn:E2.
      split.
      {
        ector. 1: ector.
        rewrite ListES_step_spec,<-Heqst1'.
        reflexivity.
      }
      eapply MITM_WDFA_ES_filter_spec with (es:=(_,_,_,_,_,_)).
      + unfold In_MITM_WDFA_ES.
        eexists.
        split.
        1: reflexivity.
        cbn.
        rewrite Hc,E2.
        exists (dl + a0)%Z. exists Z0. exists c1.
        repeat split.
        assert (A:((d1+a0) + oDir_to_Z g1 * Z.of_N c1)%Z = (dl+a0+0)%Z) by lia.
        apply A.
      + rewrite in_map_iff.
        eexists (_,_,Z0).
        split.
        -- rewrite Z.sub_0_r. reflexivity.
        -- unfold pop_r.
           apply WDFA_pop_spec; auto 1.
           ++ apply U_r_enc_inj.
           ++ apply nat_n_list_spec.
    - subst st1.
      cbn in Hd.
      destruct (WDFA_match U_r U0_r wdfa_r r0) as [r1' dr'] eqn:E0.
      destruct (wdfa_r r1' m4) as [u' a] eqn:E1.
      inversion Hd. subst u'. subst dr. clear Hd.
      destruct (wdfa_l l1 m2) as [u' a0] eqn:E2.
      split.
      {
        ector. 1: ector.
        rewrite ListES_step_spec,<-Heqst1'.
        reflexivity.
      }
      eapply MITM_WDFA_ES_filter_spec with (es:=(_,_,_,_,_,_)).
      + unfold In_MITM_WDFA_ES.
        eexists.
        split.
        1: reflexivity.
        cbn.
        rewrite E0,Hc,E2.
        exists (dl + a0)%Z. exists dr'. exists c1.
        repeat split.
        assert (A:((d1+a0-a) + oDir_to_Z g1 * Z.of_N c1)%Z = (dl+a0+dr')%Z) by lia.
        apply A.
      + rewrite in_map_iff.
        eexists (_,_,a).
        split.
        -- reflexivity.
        -- unfold pop_r.
           apply WDFA_pop_spec; auto 1.
           ++ apply U_r_enc_inj.
           ++ apply nat_n_list_spec.
  }
Qed.


Lemma MITM_WDFA_ES_step_spec tm x:
  match MITM_WDFA_ES_step tm x with
  | Some ls =>
      forall st0,
      In_MITM_WDFA_ES st0 x ->
      exists n st1 x1,
        Steps Σ tm (1 + n) st0 st1 /\ In_MITM_WDFA_ES st1 x1 /\ In x1 ls
  | None => True
  end.
Proof.
  pose proof (MITM_WDFA_ES_step_spec0 tm x) as H.
  destruct (MITM_WDFA_ES_step tm x).
  2: trivial.
  intros st0 H0.
  specialize (H st0 H0).
  destruct H as [n [st1 [Ha [x1 Hb]]]].
  exists n. exists st1. exists x1.
  tauto.
Qed.

Definition MITM_WDFA_ES_decider0:nat->HaltDecider :=
  (T_decider _ MITM_WDFA_ES_enc MITM_WDFA_InitES MITM_WDFA_ES_step).

Definition MITM_WDFA_ES_decider0_spec :=
  (T_decider_spec _ _ MITM_WDFA_ES_enc_inj In_MITM_WDFA_ES _ In_MITM_WDFA_InitES _ MITM_WDFA_ES_step_spec).

End MITMWFAR_0.


Definition make_wdfa(f:nat->Σ->(nat*Z))(n:nat)(u:nat_n n)(i:Σ) :=
  let (u0,a):=(f (nat_n_to_nat _ u) i) in
  (nat_n_from_nat n u0,a).



Definition WDFA_from_list(ls:list(nat*Z*nat*Z))(x:nat)(i:Σ):nat*Z :=
  let '(a0,a1,b0,b1) := nth x ls (O,Z0,O,Z0) in
  match i with
  | Σ0 => (a0,a1)
  | Σ1 => (b0,b1)
  end.




Definition MITM_WDFA_verifier
  (max_d:Z)
  (n_l:nat)(wdfa_l:nat->Σ->(nat*Z))
  (n_r:nat)(wdfa_r:nat->Σ->(nat*Z))
  (n:nat)
  (tm:TM Σ):HaltDecideResult :=
  let wdfa_l':=make_wdfa wdfa_l n_l in
  let wdfa_r':=make_wdfa wdfa_r n_r in
  let wdfa_sgn_l:=wdfa_sgn_rec (nat_n n_l) (nat_n_enc n_l) (nat_n_list n_l) n wdfa_l' in
  let wdfa_sgn_r:=wdfa_sgn_rec (nat_n n_r) (nat_n_enc n_r) (nat_n_list n_r) n wdfa_r' in
  if
  (wdfa_0_dec (nat_n n_l) (nat_n_O n_l) (nat_n_enc n_l) wdfa_l') &&&
  (wdfa_0_dec (nat_n n_r) (nat_n_O n_r) (nat_n_enc n_r) wdfa_r') &&&
  (wdfa_sgn_closed_dec (nat_n n_l) (nat_n_enc n_l) (nat_n_list n_l) wdfa_l' wdfa_sgn_l) &&&
  (wdfa_sgn_closed_dec (nat_n n_r) (nat_n_enc n_r) (nat_n_list n_r) wdfa_r' wdfa_sgn_r)
  then
  MITM_WDFA_ES_decider0 n_l n_r wdfa_l' wdfa_r' wdfa_sgn_l wdfa_sgn_r max_d n tm
  else
  Result_Unknown.

Lemma MITM_WDFA_verifier_spec max_d n_l wdfa_l n_r wdfa_r n:
  HaltDecider_WF (N.to_nat BB) (MITM_WDFA_verifier max_d n_l wdfa_l n_r wdfa_r n).
Proof.
  unfold HaltDecider_WF.
  intros.
  unfold MITM_WDFA_verifier.
  repeat rewrite shortcut_andb_spec.
  destruct (wdfa_0_dec (nat_n n_l) (nat_n_O n_l) (nat_n_enc n_l) (make_wdfa wdfa_l n_l)) eqn:E0.
  2: cbn; trivial.
  destruct (wdfa_0_dec (nat_n n_r) (nat_n_O n_r) (nat_n_enc n_r) (make_wdfa wdfa_r n_r)) eqn:E1.
  2: cbn; trivial.
  destruct (wdfa_sgn_closed_dec (nat_n n_l)) eqn:E2.
  2: cbn; trivial.
  destruct (wdfa_sgn_closed_dec (nat_n n_r)) eqn:E3.
  2: cbn; trivial.
  cbn.
  eapply MITM_WDFA_ES_decider0_spec; eauto 1.
  - eapply wdfa_0_dec_spec; eauto 1.
    apply nat_n_enc_inj.
  - eapply wdfa_0_dec_spec; eauto 1.
    apply nat_n_enc_inj.
  - eapply wdfa_sgn_closed_dec_spec; eauto 1.
    + apply nat_n_enc_inj.
    + apply nat_n_list_spec.
  - eapply wdfa_sgn_closed_dec_spec; eauto 1.
    + apply nat_n_enc_inj.
    + apply nat_n_list_spec.
Qed.

End MITMWFAR.


Definition TM_to_rev_NF(tm:TM Σ) :=
match tm St0 Σ0 with
| Some {| nxt:=_; dir:=Dneg; out:=_ |} => TM_rev _ tm
| _ => tm
end.

Fixpoint TM_to_TNF_NF(tm:TM Σ)(s:St)(es:ListES)(T:nat) :=
match T with
| O => tm
| S T0 =>
  match ListES_step tm es with
  | None => tm
  | Some es0 =>
    let (l0,r0,m0,s0):=es0 in
    if (St_to_nat s) <? (St_to_nat s0) then
      let s' := St_suc s in
      if St_eqb s' s0 then
        TM_to_TNF_NF tm s' es0 T0
      else
        TM_to_TNF_NF (TM_swap _ s' s0 tm) s' (Build_ListES l0 r0 m0 s') T0
    else
      TM_to_TNF_NF tm s es0 T0
  end
end.

Fixpoint TM_to_write_nonzero_first(tm:TM Σ)(T:nat) :=
match T with
| O => tm
| S T0 =>
  match tm St0 Σ0 with
  | Some {| nxt:=s'; dir:=d; out:=Σ0 |} =>
    if St_eqb St0 s' then tm
    else TM_to_write_nonzero_first (TM_swap _ St0 s' tm) T0
  | _ => tm
  end
end.

Definition TM_to_NF(tm:TM Σ) :=
  TM_simplify (TM_to_rev_NF (TM_simplify (TM_to_TNF_NF (TM_simplify (TM_to_write_nonzero_first tm 100)) St0 (Build_ListES nil nil Σ0 St0) 110))).

Lemma TM_to_rev_NF_spec tm:
  NonHalt _ tm (InitES Σ Σ0) <-> NonHalt _ (TM_to_rev_NF tm) (InitES Σ Σ0).
Proof.
  unfold TM_to_rev_NF.
  destruct (tm St0 Σ0) as [[s' [|] o]|].
  2,3: tauto.
  unfold NonHalt.
  split; intros.
  - specialize (H n).
    destruct H as [st' H].
    eexists.
    rewrite Steps_rev.
    rewrite InitES_rev.
    rewrite <-ExecState_rev_rev in H.
    apply H.
  - specialize (H n).
    destruct H as [st' H].
    eexists.
    rewrite Steps_rev in H.
    rewrite InitES_rev in H.
    apply H.
Qed.

Lemma TM_to_TNF_NF_spec tm s es T:
  NonHalt _ tm (InitES Σ Σ0) <-> NonHalt _ (TM_to_TNF_NF tm s es T) (InitES Σ Σ0).
Proof.
  gd es. gd s. gd tm.
  induction T; intros.
  1: cbn; tauto.
  unfold TM_to_TNF_NF. fold TM_to_TNF_NF.
  destruct (ListES_step tm es) as [[l0 r0 m0 s1]|].
  2: tauto.
  destruct (St_to_nat s0 <? St_to_nat s1) eqn:E.
  2: apply IHT.
  destruct (St_eqb (St_suc s0) s1) eqn:E0.
  1: apply IHT.
  rewrite <-IHT.
  assert (E1:(St_suc s0)<>St0) by (destruct s0; cbn; cg).
  assert (E2:s1 <> St0) by (intro X; subst; cbn in E; cg).
  assert (E3:St_suc s0 <> s1) by (intro X; subst; St_eq_dec (St_suc s0) (St_suc s0); cg).
  unfold NonHalt.
  split; intros.
  - specialize (H n).
    destruct H as [st' H].
    eexists.
    rewrite Steps_swap. 2: auto 1.
    cbn.
    unfold St_swap.
    St_eq_dec (St_suc s0) St0; cg.
    St_eq_dec s1 St0; cg.
    unfold InitES in H.
    erewrite <-ExecState_swap_swap in H.
    1: apply H.
    auto 1.
  - specialize (H n).
    destruct H as [st' H].
    eexists.
    rewrite Steps_swap in H. 2: auto 1.
    cbn in H.
    unfold St_swap in H.
    St_eq_dec (St_suc s0) St0; cg.
    St_eq_dec s1 St0; cg.
    unfold InitES.
    apply H.
Qed.

Lemma TM_to_write_nonzero_first_spec tm T:
  NonHalt _ tm (InitES Σ Σ0) <-> NonHalt _ (TM_to_write_nonzero_first tm T) (InitES Σ Σ0).
Proof.
  gd tm.
  induction T; intros.
  1: cbn; tauto.
  unfold TM_to_write_nonzero_first. fold TM_to_write_nonzero_first.
  destruct (tm St0 Σ0) as [[s' d o]|] eqn:E.
  2: tauto.
  destruct o; try tauto.
  St_eq_dec St0 s'.
  1: tauto.
  rename H into E0.
  rewrite <-IHT.
  unfold NonHalt.
  assert (E1:forall n st',
  Steps Σ tm (S n) (InitES Σ Σ0) st' <->
  Steps Σ (TM_swap Σ St0 s' tm) n (InitES Σ Σ0) (ExecState_swap _ St0 s' st')). {
  intro n.
  induction n.
  - intros.
    split; intro.
    + invst H.
      invst H1.
      cbn in H3.
      rewrite E in H3.
      invst H3.
      cbn.
      unfold St_swap.
      St_eq_dec St0 s'; cg.
      St_eq_dec s' s'; cg.
      unfold InitES.
      replace (mov Σ (upd Σ (fun _ : Z => Σ0) Σ0) d) with (fun _:Z => Σ0).
      1: ctor.
      fext.
      unfold mov,upd.
      destruct ((x + Dir_to_Z d =? 0)%Z); reflexivity.
    + ector.
      1: ctor.
      invst H.
      unfold InitES in H1.
      destruct st' as [s0 t0].
      cbn in H1.
      invst H1.
      cbn.
      rewrite E.
      f_equal.
      f_equal.
      2: unfold mov,upd; fext; destruct ((x + Dir_to_Z d =? 0)%Z); reflexivity.
      unfold St_swap in H2.
      St_eq_dec St0 s0; cg.
      St_eq_dec s' s0; cg.
  - intros.
    split; intro.
    + invst H.
      rewrite IHn in H1.
      ector; eauto 1.
      rewrite step_swap. 2: auto 1.
      rewrite ExecState_swap_swap. 2: auto 1.
      rewrite ExecState_swap_swap. 2: auto 1.
      apply H3.
    + invst H.
      ector.
      * rewrite IHn.
        erewrite <-ExecState_swap_swap in H1.
        1: apply H1.
        auto 1.
      * rewrite step_swap in H3. 2: auto 1.
        rewrite ExecState_swap_swap in H3; auto 1.
  }
  split; intros.
  - specialize (H (S n)).
    destruct H as [st' H].
    rewrite E1 in H.
    eexists.
    apply H.
  - specialize (H (Nat.pred n)).
    destruct H as [st' H].
    destruct n.
    + eexists. ector.
    + eexists.
      rewrite E1.
      erewrite <-ExecState_swap_swap in H.
      1: apply H.
      auto 1.
Qed.

Lemma TM_to_NF_spec tm:
  NonHalt _ tm (InitES Σ Σ0) <-> NonHalt _ (TM_to_NF tm) (InitES Σ Σ0).
Proof.
  unfold TM_to_NF.
  repeat rewrite TM_simplify_spec.
  rewrite <-TM_to_rev_NF_spec.
  rewrite <-TM_to_TNF_NF_spec.
  rewrite <-TM_to_write_nonzero_first_spec.
  tauto.
Qed.


Definition Finned1 := makeTM BR1 EL0 CR1 BR1 DR1 CL1 EL0 BR0 HR1 AL1.
Definition Finned2 := makeTM BR1 AR1 CR1 BL1 DL0 AR0 AR1 EL1 HR1 DL0.
Definition Finned3 := makeTM BR1 ER1 CL1 BR1 AR0 DL0 BL1 DL1 HR1 AR0.
Definition Finned4 := makeTM BR1 AL1 CL0 ER0 HR1 DL1 AR1 CL0 AR1 ER1.
Definition Finned5 := makeTM BR1 AL1 CL0 ER0 HR1 DL1 AL1 CL0 AR1 ER1.
Definition Skelet1 := makeTM BR1 DR1 CL1 CR0 AR1 DL1 ER0 BL0 HR1 CR1.
Definition Skelet10 := makeTM BR1 AR0 CL0 AR1 ER1 DL1 CL1 DL0 HR1 BR0.
Definition Skelet15 := makeTM BR1 HR1 CR1 BL1 DL1 ER1 BL1 DL0 AR1 CR0.
Definition Skelet17 := makeTM BR1 HR1 CL0 ER1 DL0 CL1 AR1 BL1 BR0 AR0.
Definition Skelet26 := makeTM BR1 DL1 CR1 BR0 AL1 CR1 EL1 AL0 CL1 HR1.
Definition Skelet33 := makeTM BR1 CL1 CR0 BR0 DL1 AL0 EL1 HR1 AL1 ER1.
Definition Skelet34 := makeTM BR1 CL1 CR0 BR0 DL1 AL0 EL1 HR1 AL1 AR1.
Definition Skelet35 := makeTM BR1 CL1 CR0 BR0 DL1 AL0 EL1 HR1 AL1 AL0.

From BusyCoq Require Import
  Finned1 Finned2 Finned3 Finned4 Finned5
  Skelet1 Skelet10 Skelet15 Skelet17 Skelet26 Skelet33 Skelet34 Skelet35.

Module Translation.
Import Individual52.Individual52.Permute.Flip.Compute.TM.

Definition to_St(x:Q):St :=
  match x with
  | BB52.A => St0
  | BB52.B => St1
  | BB52.C => St2
  | BB52.D => St3
  | BB52.E => St4
  end.

Definition of_St(x:St):Q :=
  match x with
  | St0 => BB52.A
  | St1 => BB52.B
  | St2 => BB52.C
  | St3 => BB52.D
  | St4 => BB52.E
  end.

Definition to_Σ(x:Sym):Σ :=
  match x with
  | BB52.S0 => Σ0
  | BB52.S1 => Σ1
  end.

Definition of_Σ(x:Σ):Sym :=
  match x with
  | Σ0 => BB52.S0
  | Σ1 => BB52.S1
  end.

Definition to_Dir(x:TM.dir):Dir :=
  match x with
  | TM.L => Dneg
  | TM.R => Dpos
  end.

Definition to_halftape(x:side):nat->Σ :=
  fun n => to_Σ (Streams.Str_nth n x).

Definition to_tape(x:tape):BinInt.Z->Σ :=
  let '(l0,m0,r0):=x in
    make_tape (to_halftape l0) (to_Σ m0) (to_halftape r0).

Definition to_ExecState(x:Q*tape):ExecState Σ :=
  let (s0,t0):=x in
  (to_St s0,to_tape t0).

Definition to_oTrans(x:option (Sym*TM.dir*Q)):option (Trans Σ) :=
  match x with
  | None => None
  | Some (o,d,s) => Some {| nxt:=to_St s; dir:=to_Dir d; out:=to_Σ o |}
  end.

Definition to_TM(tm:TM):BB52Statement.TM Σ :=
  fun s0 i0 =>
  to_oTrans (tm (of_St s0,of_Σ i0)).

Lemma of_to_St s0:
  of_St (to_St s0) = s0.
Proof.
  destruct s0; reflexivity.
Qed.

Lemma of_to_Σ s0:
  of_Σ (to_Σ s0) = s0.
Proof.
  destruct s0; reflexivity.
Qed.

Lemma to_TM_spec tm s0 i0:
  to_TM tm (to_St s0) (to_Σ i0) = to_oTrans (tm (s0, i0)).
Proof.
  unfold to_TM.
  rewrite of_to_St,of_to_Σ.
  reflexivity.
Qed.

Lemma Str_nth_S {T} n (x:Streams.Stream T):
  Streams.Str_nth (S n) x = Streams.Str_nth n (Streams.tl x).
Proof.
  replace (S n) with (n+1) by lia.
  rewrite <-Streams.Str_nth_plus.
  reflexivity.
Qed.

Lemma Str_nth_S' {T} n a (x:Streams.Stream T):
  Streams.Str_nth n x =
  Streams.Str_nth (S n) (Streams.Cons a x).
Proof.
  replace (S n) with (n+1) by lia.
  rewrite <-Streams.Str_nth_plus.
  reflexivity.
Qed.

Lemma to_step tm st0 st1:
  step tm st0 st1 ->
  BB52Statement.step Σ (to_TM tm) (to_ExecState st0) = Some (to_ExecState st1).
Proof.
  intro H.
  invst H.
  - unfold BB52Statement.step.
    cbn.
    rewrite to_TM_spec,H0.
    cbn.
    f_equal.
    f_equal.
    unfold mov,upd,make_tape,Dir_to_Z.
    fext.
    assert (E:(x<0\/x=0\/x=1\/x>1)%Z) by lia.
    destruct E as [E|[E|[E|E]]].
    + destruct (x + -1)%Z eqn:E0; try lia.
      cbn.
      destruct x eqn:E1; try lia.
      unfold to_halftape. f_equal.
      replace (Nat.pred (Pos.to_nat p)) with (S (Nat.pred (Pos.to_nat p0))) by lia.
      apply Str_nth_S.
    + subst x. cbn.
      unfold to_halftape. f_equal.
    + subst x. cbn.
      unfold to_halftape. f_equal.
    + destruct (x + -1)%Z eqn:E0; try lia.
      cbn.
      destruct x eqn:E1; try lia.
      unfold to_halftape. f_equal.
      replace (Nat.pred (Pos.to_nat p0)) with (S (Nat.pred (Pos.to_nat p))) by lia.
      apply Str_nth_S'.
  - unfold BB52Statement.step.
    cbn.
    rewrite to_TM_spec,H0.
    cbn.
    f_equal.
    f_equal.
    unfold mov,upd,make_tape,Dir_to_Z.
    fext.
    assert (E:(x>0\/x=0\/x=-1\/x<(-1))%Z) by lia.
    destruct E as [E|[E|[E|E]]].
    + destruct (x + 1)%Z eqn:E0; try lia.
      cbn.
      destruct x eqn:E1; try lia.
      unfold to_halftape. f_equal.
      replace (Nat.pred (Pos.to_nat p)) with (S (Nat.pred (Pos.to_nat p0))) by lia.
      apply Str_nth_S.
    + subst x. cbn.
      unfold to_halftape. f_equal.
    + subst x. cbn.
      unfold to_halftape. f_equal.
    + destruct (x + 1)%Z eqn:E0; try lia.
      cbn.
      destruct x eqn:E1; try lia.
      unfold to_halftape. f_equal.
      replace (Nat.pred (Pos.to_nat p0)) with (S (Nat.pred (Pos.to_nat p))) by lia.
      apply Str_nth_S'.
Qed.


Lemma to_Steps tm n st0 st1:
  multistep tm n st0 st1 -> Steps Σ (to_TM tm) n (to_ExecState st0) (to_ExecState st1).
Proof.
  gd st0. gd st1.
  induction n; intros.
  - intros.
    invst H.
    ctor.
  - intros.
    invst H.
    specialize (IHn _ _ H2).
    replace (S n) with (n+1) by lia.
    eapply Steps_trans; eauto 1.
    ector.
    1: ctor.
    apply to_step,H1.
Qed.

Lemma Str_nth_tl_const{T} n (s0:T):
  Streams.Str_nth_tl n (Streams.const s0) = (Streams.const s0).
Proof.
  induction n.
  - reflexivity.
  - cbn. apply IHn.
Qed.

Lemma Str_nth_const{T} n (s0:T):
  Streams.Str_nth n (Streams.const s0) = s0.
Proof.
  rewrite <-(Streams.Str_nth_plus 0 n).
  rewrite Str_nth_tl_const.
  reflexivity.
Qed.


Lemma to_InitES:
  to_ExecState c0 = InitES Σ Σ0.
Proof.
  unfold c0,q0,tape0,InitES.
  cbn.
  f_equal.
  fext.
  destruct x; cbn.
  1: reflexivity.
  all: unfold to_halftape;
    rewrite Str_nth_const;
    reflexivity.
Qed.

Lemma halted_dec tm st:
  halted tm st \/
  ~halted tm st.
Proof.
  unfold halted.
  destruct st as [q [[_ s2] _]].
  destruct (tm (q,s2)).
  - right; cg.
  - left; cg.
Qed.

Lemma nonhalt_multistep tm st0:
  ~halts tm st0 ->
  forall n, exists st1, multistep tm n st0 st1.
Proof.
  unfold halts.
  intros H n.
  induction n.
  1: eexists; ctor.
  destruct IHn as [st1 IHn].
  unfold halts_in in H.
  destruct (halted_dec tm st1).
  - assert (X:False). {
      apply H.
      eexists. eexists.
      split; eauto 1.
    }
    contradiction.
  - destruct (no_halted_step _ _ H0) as [st2 H1].
    exists st2.
    replace (S n) with (n+1) by lia.
    eapply multistep_trans; eauto 1.
    ector; eauto 1.
Qed.

Lemma to_NonHalt tm:
  ~halts tm c0 ->
  ~HaltsFromInit Σ Σ0 (to_TM tm).
Proof.
  intro H.
  unfold HaltsFromInit.
  rewrite <-NonHalt_iff.
  unfold NonHalt.
  intro n.
  destruct (nonhalt_multistep _ _ H n) as [st1 H0].
  exists (to_ExecState st1).
  rewrite <-to_InitES.
  apply to_Steps,H0.
Qed.

Ltac translate_nonhalt x2 x3 :=
  match goal with
  | |- ~HaltsFromInit Σ Σ0 ?x1 =>
    replace x1 with (to_TM x2);
    [ apply to_NonHalt,x3
    | fext; fext;
      match goal with
      | x:St, x0:Σ |- _ => destruct x,x0; reflexivity
      end ]
  end.

Lemma Finned1_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned1.
Proof.
  translate_nonhalt Finned1.tm Finned1.nonhalt.
Qed.

Lemma Finned2_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned2.
Proof.
  translate_nonhalt Finned2.tm Finned2.nonhalt.
Qed.

Lemma Finned3_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned3.
Proof.
  assert (H:~HaltsFromInit Σ Σ0 (to_TM Finned3.tm)) by (apply to_NonHalt,Finned3.nonhalt).
  unfold HaltsFromInit in H.
  unfold HaltsFromInit.
  rewrite <-NonHalt_iff in H.
  rewrite <-NonHalt_iff.
  rewrite TM_to_rev_NF_spec in H.
  replace (TM_to_rev_NF (to_TM Finned3.tm)) with Finned3 in H.
  1: apply H.
  fext. fext.
  destruct x,x0; reflexivity.
Qed.

Lemma Finned4_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned4.
Proof.
  translate_nonhalt Finned4.tm Finned4.nonhalt.
Qed.

Lemma Finned5_nonhalt:
  ~HaltsFromInit Σ Σ0 Finned5.
Proof.
  translate_nonhalt Finned5.tm Finned5.nonhalt.
Qed.

Lemma Skelet10_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet10.
Proof.
  translate_nonhalt Skelet10.tm Skelet10.nonhalt.
Qed.

Lemma Skelet15_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet15.
Proof.
  translate_nonhalt Skelet15.tm Skelet15.nonhalt.
Qed.

Lemma Skelet26_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet26.
Proof.
  translate_nonhalt Skelet26.tm Skelet26.nonhalt.
Qed.

Lemma Skelet33_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet33.
Proof.
  translate_nonhalt Skelet33.tm Skelet33.nonhalt.
Qed.

Lemma Skelet34_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet34.
Proof.
  translate_nonhalt Skelet34.tm Skelet34.nonhalt.
Qed.

Lemma Skelet35_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet35.
Proof.
  translate_nonhalt Skelet35.tm Skelet35.nonhalt.
Qed.

Lemma Skelet1_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet1.
Proof.
  translate_nonhalt Skelet1.tm Skelet1.nonhalt.
Qed.

Lemma Skelet17_nonhalt:
  ~HaltsFromInit Σ Σ0 Skelet17.
Proof.
  translate_nonhalt Skelet17.tm Skelet17.nonhalt.
Qed.

End Translation.



Definition tm_holdouts_13 :=
  Finned1::Finned2::Finned3::Finned4::Finned5::
  Skelet1::Skelet10::Skelet15::Skelet17::Skelet26::Skelet33::Skelet34::Skelet35::
  nil.

Lemma tm_holdouts_13_spec:
  forall tm, In tm tm_holdouts_13 -> ~HaltsFromInit Σ Σ0 tm.
Proof.
  intros.
  cbn in H.
  destruct H as [H|H].
  1: subst; apply Translation.Finned1_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Finned2_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Finned3_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Finned4_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Finned5_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Skelet1_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Skelet10_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Skelet15_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Skelet17_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Skelet26_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Skelet33_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Skelet34_nonhalt.
  destruct H as [H|H].
  1: subst; apply Translation.Skelet35_nonhalt.
  contradiction.
Qed.

Definition Trans_eqb(tr1 tr2:Trans Σ):bool :=
  let (s1,d1,o1):=tr1 in
  let (s2,d2,o2):=tr2 in
  St_eqb s1 s2 &&&
  Dir_eqb d1 d2 &&&
  Σ_eqb o1 o2.

Lemma Trans_eqb_spec tr1 tr2:
  if Trans_eqb tr1 tr2 then tr1=tr2 else tr1<>tr2.
Proof.
  destruct tr1 as [s1 d1 o1].
  destruct tr2 as [s2 d2 o2].
  cbn.
  repeat rewrite shortcut_andb_spec.
  St_eq_dec s1 s2.
  - Dir_eq_dec d1 d2.
    + Σ_eq_dec o1 o2.
      * cbn. cg.
      * cbn. cg.
    + cbn. cg.
  - cbn. cg.
Qed.

Ltac Trans_eq_dec s1 s2 := eq_dec Trans_eqb_spec Trans_eqb s1 s2.

Definition option_eqb {T}(f:T->T->bool) (t1 t2:option T):bool :=
match t1,t2 with
| Some c1,Some c2 => f c1 c2
| None,None => true
| _,_ => false
end.

Lemma option_eqb_spec {T}(f:T->T->bool)(f_spec:forall t1 t2, if f t1 t2 then t1=t2 else t1<>t2) a1 a2:
  if option_eqb f a1 a2 then a1=a2 else a1<>a2.
Proof.
  destruct a1 as [a1|];
  destruct a2 as [a2|].
  - cbn.
    specialize (f_spec a1 a2).
    destruct (f a1 a2); cg.
  - cbn. cg.
  - cbn. cg.
  - cbn. cg.
Qed.

Ltac option_eq_dec f f_spec o1 o2 := eq_dec (option_eqb_spec f f_spec) (option_eqb f) o1 o2.

Definition tm_eqb(tm0 tm1:TM Σ):bool :=
  forallb_St (fun s0 =>
  forallb_Σ (fun i0 =>
  option_eqb Trans_eqb (tm0 s0 i0) (tm1 s0 i0))).

Lemma tm_eqb_spec (tm0 tm1:TM Σ):
  if tm_eqb tm0 tm1 then tm0=tm1 else tm0<>tm1.
Proof.
  unfold tm_eqb.
  destruct (
    forallb_St (fun s0 =>
    forallb_Σ (fun i0 =>
    option_eqb Trans_eqb (tm0 s0 i0) (tm1 s0 i0)))) eqn:E.
  - fext.
    fext.
    rewrite forallb_St_spec in E.
    specialize (E x).
    rewrite forallb_Σ_spec in E.
    specialize (E x0).
    option_eq_dec Trans_eqb Trans_eqb_spec (tm0 x x0) (tm1 x x0); cg.
  - intro X. subst.
    assert (forallb_St
        (fun s0 : St => forallb_Σ (fun i0 : Σ => option_eqb Trans_eqb (tm1 s0 i0) (tm1 s0 i0))) = true). {
      rewrite forallb_St_spec.
      intro s0.
      rewrite forallb_Σ_spec.
      intro i0.
      option_eq_dec Trans_eqb Trans_eqb_spec (tm1 s0 i0) (tm1 s0 i0); cg.
    }
    cg.
Qed.

Fixpoint find_tm(tm:TM Σ)(ls:list (TM Σ)):bool :=
match ls with
| nil => false
| h::t => tm_eqb tm h ||| find_tm tm t
end.

Lemma find_tm_spec tm ls:
  find_tm tm ls = true ->
  In tm ls.
Proof.
  induction ls.
  1: cbn; cg.
  unfold find_tm. fold find_tm.
  intro H.
  rewrite shortcut_orb_spec in H.
  rewrite Bool.orb_true_iff in H.
  destruct H as [H|H].
  - left.
    pose proof (tm_eqb_spec tm a).
    destruct (tm_eqb tm a); cg.
  - right.
    apply IHls,H.
Qed.

Definition holdout_checker tm := if find_tm tm tm_holdouts_13 then Result_NonHalt else Result_Unknown.

Lemma holdout_checker_spec n: HaltDecider_WF n holdout_checker.
Proof.
  unfold HaltDecider_WF.
  intro tm.
  unfold holdout_checker.
  pose proof (find_tm_spec tm tm_holdouts_13) as H.
  destruct (find_tm tm tm_holdouts_13).
  2: trivial.
  specialize (H eq_refl).
  apply tm_holdouts_13_spec,H.
Qed.

Inductive DeciderType :=
| NG(hlen len:nat)
| NG_LRU(len:nat)
| RWL(len m:nat)
| DNV(n:nat)(f:nat->Σ->nat)
| WA(max_d:BinNums.Z)(n_l:nat)(f_l:nat->Σ->(nat*BinNums.Z))(n_r:nat)(f_r:nat->Σ->(nat*BinNums.Z))
| Ha
| Lp1
| Holdout.


Definition getDecider(x:DeciderType) :=
match x with
| NG hlen len =>
  match hlen with
  | O => NGramCPS_decider_impl2 len len 5000001
  | _ => NGramCPS_decider_impl1 hlen len len 5000001
  end
| NG_LRU len =>
  NGramCPS_LRU_decider len len 5000001
| RWL len mnc => RepWL_ES_decider len mnc 320 150001
| DNV n f => dfa_nfa_verifier n f
| WA max_d n_l f_l n_r f_r => MITM_WDFA_verifier max_d n_l f_l n_r f_r 10000000
| Ha => halt_decider_max
| Lp1 => loop1_decider 1050000 (4096::8192::16384::32768::65536::131072::262144::524288::nil)
| Holdout => holdout_checker
end.

Lemma getDecider_spec x:
  HaltDecider_WF (N.to_nat BB) (getDecider x).
Proof.
  destruct x; unfold getDecider.
  - destruct hlen.
    + apply NGramCPS_decider_impl2_spec.
    + apply NGramCPS_decider_impl1_spec.
  - apply NGramCPS_LRU_decider_spec.
  - apply RepWL_ES_decider_spec.
  - apply dfa_nfa_verifier_spec.
  - apply MITM_WDFA_verifier_spec.
  - apply halt_decider_max_spec.
  - apply loop1_decider_WF.
    unfold BB.
    replace (Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1
        (Decimal.D0
           (Decimal.D5 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))) with
    (N.to_nat 1050000).
    1: lia.
    symmetry.
    apply nat_eqb_N_spec.
    vm_compute.
    reflexivity.
  - apply holdout_checker_spec.
Qed.


Definition tm_RWL:list ((TM Σ)*(DeciderType)) :=
(makeTM BR0 HR1 AL1 CL0 DR1 CL1 CL1 ER0 BL1 ER1,RWL 2 3)::
(makeTM BR0 HR1 AL1 CR0 DL0 CR1 ER1 DL1 CL1 BR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CR0 DL0 CR1 ER1 DL1 CR1 BR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CR0 DL0 CR1 ER1 DL1 DL1 BR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CR0 DL1 CR1 CR1 EL0 BR1 EL1,RWL 2 3)::
(makeTM BR0 HR1 AL1 CR0 DR1 CR1 EL1 BL0 CR1 DL0,RWL 9 2)::
(makeTM BR0 HR1 AL1 CL1 BR1 DL0 DR1 ER0 AL0 BR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CL1 BR1 DL0 DR1 ER0 AL0 CR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CL1 BR1 DL0 DR1 ER0 AL1 BR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CL1 BR1 DL0 DR1 ER0 AL1 CR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CL1 DL0 BR0 DR1 ER0 AL0 BR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CL1 DL0 DL0 DR1 ER0 AL0 BR1,RWL 2 2)::
(makeTM BR0 HR1 AL1 CR1 DL1 ER1 DR1 EL0 DL0 AR1,RWL 4 3)::
(makeTM BR0 HR1 CL0 AR0 DR1 CL1 BR1 EL0 DL1 EL0,RWL 28 3)::
(makeTM BR0 HR1 CL0 AR0 DR1 ER0 EL1 BL0 CR1 DL0,RWL 8 2)::
(makeTM BR0 HR1 CL0 AR1 DL1 BR0 ER1 BL0 CR1 DR1,RWL 9 2)::
(makeTM BR0 HR1 CL0 AR1 DL1 DL1 ER1 BL0 CR1 DR1,RWL 9 2)::
(makeTM BR0 HR1 CL0 AR1 DL1 DR1 ER1 DL0 CR0 BL0,RWL 12 2)::
(makeTM BR0 HR1 CL0 AR1 DR1 DL1 BR1 EL0 AR0 DL0,RWL 12 2)::
(makeTM BR0 HR1 CL0 AR1 DR1 DL1 BR1 EL0 DL0 CR0,RWL 7 3)::
(makeTM BR0 HR1 CL0 BR0 DR1 EL0 ER1 AR0 CL1 BL1,RWL 3 3)::
(makeTM BR0 HR1 CL0 BR1 DR1 CL1 BL1 ER1 HR1 BR0,RWL 2 2)::
(makeTM BR0 HR1 CL0 BR1 DR1 CL1 BR1 ER1 HR1 BR0,RWL 2 2)::
(makeTM BR0 HR1 CL0 BR1 DR1 CL1 CL1 ER1 HR1 BR0,RWL 2 2)::
(makeTM BR0 HR1 CL0 CR1 DR1 DL0 ER1 BL1 DL1 AR0,RWL 3 2)::
(makeTM BR0 HR1 CL0 DL0 DR1 BL1 ER1 CR0 DL1 AR0,RWL 6 2)::
(makeTM BR0 HR1 CL0 DR0 AL1 EL1 ER1 EL0 BR1 BL1,RWL 5 2)::
(makeTM BR0 HR1 CL0 EL0 DR1 AR0 ER1 DR0 BL1 CR0,RWL 20 2)::
(makeTM BR0 HR1 CL0 EL0 DR1 BL1 ER1 AR0 CL1 DR0,RWL 57 2)::
(makeTM BR0 HR1 CL0 ER0 DL0 AR0 EL0 EL1 CR1 DL1,RWL 2 4)::
(makeTM BR0 HR1 CL0 ER0 DL1 AL0 BR1 CL1 BR1 CR0,RWL 35 2)::
(makeTM BR0 HR1 CL0 ER0 DL1 EL1 BR1 CL1 AL0 DR0,RWL 3 2)::
(makeTM BR0 HR1 CL0 ER0 DR1 AR1 EL1 BL0 CR1 DL0,RWL 12 2)::
(makeTM BR0 HR1 CL0 ER1 DR1 DL0 BR1 DL1 AR1 CR0,RWL 4 3)::
(makeTM BR0 HR1 CR0 AR1 DR1 DL0 EL0 AR0 CL1 DL1,RWL 12 2)::
(makeTM BR0 HR1 CR0 BL0 DL0 BR1 CR1 EL0 DL1 AR1,RWL 4 2)::
(makeTM BR0 HR1 CR0 BL0 DR1 DL0 EL0 AR0 CL1 DL1,RWL 7 2)::
(makeTM BR0 HR1 CR0 BL1 DL1 CR1 AL1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 HR1 CR0 BL1 DL1 CR1 BL1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 HR1 CR0 BL1 DL1 CR1 BR1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 HR1 CR0 BL1 DL1 CR1 CR1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 HR1 CR0 BR1 DL0 AR1 EL1 EL0 BR1 CL0,RWL 35 2)::
(makeTM BR0 HR1 CR0 BR1 DR1 EL0 CL1 AR1 CL1 EL0,RWL 8 3)::
(makeTM BR0 HR1 CR0 BR1 DR1 EL0 EL1 AR1 CL1 EL0,RWL 8 3)::
(makeTM BR0 HR1 CR0 CL0 DR1 AL1 ER0 CR0 EL1 BL0,RWL 5 3)::
(makeTM BR0 HR1 CR0 CL1 DR1 BL0 EL0 DR0 CR1 EL1,RWL 2 3)::
(makeTM BR0 HR1 CR0 DL0 DL0 BR1 CR1 EL0 DL1 AR1,RWL 4 2)::
(makeTM BR0 HR1 CR0 DL0 DL1 ER1 BL1 AR1 DR1 BR1,RWL 3 3)::
(makeTM BR0 HR1 CR0 DL0 DR1 ER1 EL1 AR1 CR1 BL1,RWL 2 2)::
(makeTM BR0 HR1 CR0 DL1 AL1 BR1 BL1 EL0 ER1 CL0,RWL 1 4)::
(makeTM BR0 HR1 CR0 EL0 DL0 BR1 CR1 DL1 BL0 AR1,RWL 7 2)::
(makeTM BR0 HR1 CR0 EL1 DL1 ER0 CR1 BL0 DL0 AL0,RWL 6 2)::
(makeTM BR0 HR1 CL1 AR1 DR0 BL0 EL1 DR1 AL0 CL0,RWL 2 2)::
(makeTM BR0 HR1 CL1 AR1 DR0 BL0 EL1 DR1 BL1 CL0,RWL 2 2)::
(makeTM BR0 HR1 CL1 AR1 DR1 CL0 ER0 ER0 BR1 BL0,RWL 4 2)::
(makeTM BR0 HR1 CL1 BL0 DL0 ER0 DR1 CL0 AR1 BR1,RWL 6 2)::
(makeTM BR0 HR1 CL1 BL0 DR0 BL0 ER1 CR1 BR1 AR1,RWL 4 3)::
(makeTM BR0 HR1 CL1 BL0 DR1 EL0 ER0 CR0 BL1 AL0,RWL 4 2)::
(makeTM BR0 HR1 CL1 BR1 AL1 DL0 AR1 EL0 CL0 BR1,RWL 6 2)::
(makeTM BR0 HR1 CL1 BR1 AL1 DL0 EL0 DL1 AR1 AR0,RWL 2 3)::
(makeTM BR0 HR1 CL1 BR1 AL1 DL1 HR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 HR1 CL1 BR1 AL1 DL1 AR0 EL0 DL0 EL1,RWL 2 2)::
(makeTM BR0 HR1 CL1 BR1 BR1 DL0 AR1 EL1 CR0 DL1,RWL 2 3)::
(makeTM BR0 HR1 CL1 BR1 BR1 DL0 ER0 DL1 AR1 EL0,RWL 2 3)::
(makeTM BR0 HR1 CL1 BR1 BR1 DL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 HR1 CL1 BR1 BR1 DL1 HR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 HR1 CL1 BR1 BR1 DL1 AR0 EL0 DL0 EL1,RWL 2 2)::
(makeTM BR0 HR1 CL1 BR1 DL0 ER1 DR1 CL0 BR0 AR1,RWL 4 2)::
(makeTM BR0 HR1 CL1 BR1 DL0 ER1 DR1 CL0 EL0 AR1,RWL 4 2)::
(makeTM BR0 HR1 CL1 BR1 DL1 DL0 ER0 EL0 AR1 CR1,RWL 2 3)::
(makeTM BR0 HR1 CL1 BR1 DL1 DL0 EL1 AR0 CR1 CL0,RWL 1 4)::
(makeTM BR0 HR1 CL1 BR1 DL1 ER0 EL0 CL0 AL1 CR1,RWL 44 2)::
(makeTM BR0 HR1 CL1 BR1 DL1 EL1 BR0 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 HR1 CL1 BR1 DL1 EL1 EL0 DL1 AR0 DL0,RWL 2 2)::
(makeTM BR0 HR1 CL1 BR1 DR1 EL1 BR0 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 HR1 CL1 BR1 DR1 EL1 EL0 DL1 AR0 DL0,RWL 2 2)::
(makeTM BR0 HR1 CL1 CL0 DR0 CL1 EL1 DR1 HR1 BL1,RWL 2 2)::
(makeTM BR0 HR1 CL1 CL0 DR1 AR0 ER1 DL1 BR1 BL0,RWL 2 3)::
(makeTM BR0 HR1 CL1 CL0 DR1 CL1 HR1 ER0 BL1 ER1,RWL 2 3)::
(makeTM BR0 HR1 CL1 CL0 DR1 DL0 EL0 ER1 BL1 AR1,RWL 2 4)::
(makeTM BR0 HR1 CL1 CL0 DR1 ER1 EL1 CR1 AR0 BL0,RWL 6 2)::
(makeTM BR0 HR1 CL1 CR0 AL1 DL0 ER1 DL1 BR1 EL0,RWL 6 2)::
(makeTM BR0 HR1 CL1 CR1 DL0 DL1 AR1 ER0 BL1 AL0,RWL 3 2)::
(makeTM BR0 HR1 CL1 CR1 DL0 EL0 AR1 BR1 DL1 BR0,RWL 2 3)::
(makeTM BR0 HR1 CL1 CR1 DL1 AR0 ER1 DL0 AR1 ER1,RWL 10 2)::
(makeTM BR0 HR1 CL1 CR1 DR1 CL0 AR1 EL1 CR1 EL1,RWL 2 4)::
(makeTM BR0 HR1 CL1 CR1 DR1 DL0 ER1 DL1 AR0 CL0,RWL 6 2)::
(makeTM BR0 HR1 CL1 CR1 DR1 EL0 AR0 ER0 BL1 DL0,RWL 5 3)::
(makeTM BR0 HR1 CL1 DL0 DR0 BL1 AR1 ER1 CL0 CR1,RWL 6 3)::
(makeTM BR0 HR1 CL1 DL0 DR1 AR1 EL0 CR0 BL1 ER1,RWL 2 3)::
(makeTM BR0 HR1 CL1 DR0 CR0 DL1 EL0 ER1 AR1 BL0,RWL 4 2)::
(makeTM BR0 HR1 CL1 DR0 DL0 AL0 EL0 DL1 AR1 BL1,RWL 10 2)::
(makeTM BR0 HR1 CL1 DR0 DL0 CL0 AR1 ER0 BL1 DR1,RWL 4 3)::
(makeTM BR0 HR1 CL1 DR0 DL1 AL0 BR1 ER0 EL1 CL0,RWL 14 2)::
(makeTM BR0 HR1 CL1 DR0 DL1 AL0 BR1 ER1 CR0 EL0,RWL 5 3)::
(makeTM BR0 HR1 CL1 DL1 BR1 AR0 EL0 AL1 ER1 CL0,RWL 2 2)::
(makeTM BR0 HR1 CL1 DL1 DR1 CR0 EL1 CR0 AR1 EL0,RWL 2 3)::
(makeTM BR0 HR1 CL1 DR1 AL1 EL1 BR1 CR0 CL0 DL0,RWL 2 2)::
(makeTM BR0 HR1 CL1 DR1 DL0 DR0 AR1 ER0 EL1 BL1,RWL 1 4)::
(makeTM BR0 HR1 CL1 DR1 DL1 ER0 BR1 CL0 BL0 AR1,RWL 8 2)::
(makeTM BR0 HR1 CL1 EL0 DR0 CR1 ER1 BR1 BL1 AR1,RWL 4 3)::
(makeTM BR0 HR1 CL1 EL0 DR1 BR0 ER1 CR1 BL1 AR0,RWL 11 2)::
(makeTM BR0 HR1 CL1 ER0 CR1 DL1 CL1 EL0 AR1 CL0,RWL 13 2)::
(makeTM BR0 HR1 CL1 ER0 DL0 AL0 AL1 EL0 BR1 EL1,RWL 1 3)::
(makeTM BR0 HR1 CL1 ER0 DL0 AR1 DR1 CL0 AR1 DL0,RWL 5 3)::
(makeTM BR0 HR1 CL1 ER0 DL0 CL1 AR1 BL1 DR1 DL0,RWL 3 4)::
(makeTM BR0 HR1 CL1 ER0 DL0 DR0 AR1 BL1 DR1 DL0,RWL 3 4)::
(makeTM BR0 HR1 CL1 ER0 DL0 EL1 AR1 BL0 DL0 DR1,RWL 4 2)::
(makeTM BR0 HR1 CL1 ER0 DL0 ER1 BR1 BL0 AR1 CR1,RWL 2 3)::
(makeTM BR0 HR1 CL1 ER0 DR0 CL0 BL1 DR1 EL0 BR1,RWL 2 3)::
(makeTM BR0 HR1 CL1 ER0 DL1 CL1 BR1 DL0 AR1 CR0,RWL 3 4)::
(makeTM BR0 HR1 CL1 ER0 DR1 CL1 HR1 BR1 CL0 ER1,RWL 2 2)::
(makeTM BR0 HR1 CL1 ER0 DR1 DL0 EL0 CL1 CR0 AR1,RWL 3 2)::
(makeTM BR0 HR1 CL1 ER1 DR0 BL1 BR1 CR1 AR1 EL0,RWL 21 2)::
(makeTM BR0 HR1 CL1 ER1 DR0 CL0 BL1 BR1 AR1 DL1,RWL 4 3)::
(makeTM BR0 HR1 CL1 ER1 DR0 CL0 BL1 BR1 AR1 ER1,RWL 4 3)::
(makeTM BR0 HR1 CR1 AL0 DL1 ER1 DR1 EL0 DL0 AR1,RWL 4 2)::
(makeTM BR0 HR1 CR1 AR1 CL0 DR1 DL1 EL0 BR1 BL0,RWL 8 2)::
(makeTM BR0 HR1 CR1 AR1 DL0 BR1 DR1 EL0 DL1 CL1,RWL 6 2)::
(makeTM BR0 HR1 CR1 AR1 DR0 BR1 ER1 EL0 DL1 CL1,RWL 10 2)::
(makeTM BR0 HR1 CR1 AR1 DL1 EL0 BR1 CL0 DL1 DL1,RWL 6 2)::
(makeTM BR0 HR1 CR1 AR1 DL1 EL0 BR1 CL0 ER1 DL1,RWL 6 2)::
(makeTM BR0 HR1 CR1 AR1 DL1 EL1 BR1 CL0 CR1 DR0,RWL 6 2)::
(makeTM BR0 HR1 CR1 AR1 DL1 EL1 BR1 CL0 DR0 CR0,RWL 6 2)::
(makeTM BR0 HR1 CR1 AR1 DL1 EL1 BR1 CL0 DR0 DR0,RWL 6 2)::
(makeTM BR0 HR1 CR1 AR1 DL1 EL1 ER0 CL0 BR1 DR1,RWL 4 3)::
(makeTM BR0 HR1 CR1 AR1 DL1 EL1 ER1 CL0 BR0 DR1,RWL 2 4)::
(makeTM BR0 HR1 CR1 AR1 DR1 DL1 EL0 DR0 AR1 CL0,RWL 7 2)::
(makeTM BR0 HR1 CR1 BL0 CL1 DR0 ER1 EL0 BL1 AR0,RWL 6 2)::
(makeTM BR0 HR1 CR1 BL0 DL0 DR0 ER1 BL1 BL1 AR0,RWL 6 2)::
(makeTM BR0 HR1 CR1 BR0 DL1 BR0 ER1 EL0 CL0 AR0,RWL 8 3)::
(makeTM BR0 HR1 CR1 BR0 DL1 ER0 EL0 CL0 BR1 AL0,RWL 4 2)::
(makeTM BR0 HR1 CR1 BL1 BL1 DR0 EL1 DR1 HR1 BL0,RWL 2 3)::
(makeTM BR0 HR1 CR1 BL1 BL1 DR1 HR1 ER0 BL0 ER1,RWL 2 2)::
(makeTM BR0 HR1 CR1 BL1 DR0 ER1 DL1 BL0 AR0 EL0,RWL 2 3)::
(makeTM BR0 HR1 CR1 BL1 DL1 ER1 BL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR0 HR1 CR1 BL1 DR1 ER1 BL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR0 HR1 CR1 BR1 DL0 CL1 AR0 EL0 BL1 DL1,RWL 2 2)::
(makeTM BR0 HR1 CR1 BR1 DL1 CL0 AR1 EL1 DL0 ER0,RWL 9 2)::
(makeTM BR0 HR1 CR1 BR1 DL1 DR0 AL1 EL0 BL1 CL1,RWL 2 4)::
(makeTM BR0 HR1 CR1 CL0 DL1 CR0 ER1 DL0 BL0 AR0,RWL 4 2)::
(makeTM BR0 HR1 CR1 CR0 DL0 CR1 ER1 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 HR1 CR1 CR0 DL0 EL0 BL1 EL1 CL1 AR1,RWL 6 2)::
(makeTM BR0 HR1 CR1 CR0 DL0 ER0 AR1 EL1 CL1 AL0,RWL 4 3)::
(makeTM BR0 HR1 CR1 CR0 DL1 CR1 HR1 EL0 BR1 EL1,RWL 2 3)::
(makeTM BR0 HR1 CR1 CR0 DL1 EL0 AL0 CL1 BL1 AR1,RWL 5 3)::
(makeTM BR0 HR1 CR1 CR0 DL1 EL0 CL1 EL1 BL1 AR1,RWL 5 2)::
(makeTM BR0 HR1 CR1 CR0 DL1 EL0 DL1 EL1 BL1 AR1,RWL 5 2)::
(makeTM BR0 HR1 CR1 CR0 DL1 EL1 DR1 EL0 DL0 AR1,RWL 2 2)::
(makeTM BR0 HR1 CR1 CR0 DR1 EL0 ER1 AR1 CL1 DL0,RWL 4 2)::
(makeTM BR0 HR1 CR1 CL1 DL0 ER0 AL0 BL1 BR1 BL0,RWL 5 2)::
(makeTM BR0 HR1 CR1 CL1 DR1 ER0 BL1 DL0 AR0 DL1,RWL 2 3)::
(makeTM BR0 HR1 CR1 CR1 DL1 ER1 DR1 EL0 DL0 AR1,RWL 4 2)::
(makeTM BR0 HR1 CR1 DL0 DL0 ER1 AR1 BL1 DL1 AR0,RWL 4 2)::
(makeTM BR0 HR1 CR1 DL0 DL0 ER1 AR1 BL1 DL1 AR1,RWL 4 3)::
(makeTM BR0 HR1 CR1 DL0 DR0 CR0 EL1 AL0 BL0 BL1,RWL 12 2)::
(makeTM BR0 HR1 CR1 DL0 DR0 CR0 EL1 AL0 BL0 EL1,RWL 6 2)::
(makeTM BR0 HR1 CR1 DL0 DR0 EL1 EL1 AR1 BL0 ER0,RWL 6 2)::
(makeTM BR0 HR1 CR1 DL0 DL1 EL0 ER0 CL0 BL1 AR1,RWL 2 2)::
(makeTM BR0 HR1 CR1 DL0 DR1 AR0 BL1 EL0 DR1 BL0,RWL 4 2)::
(makeTM BR0 HR1 CR1 DL0 DR1 AR0 BL1 EL1 AL1 BL0,RWL 4 2)::
(makeTM BR0 HR1 CR1 DL0 DR1 AR0 BL1 EL1 AL1 CR1,RWL 4 2)::
(makeTM BR0 HR1 CR1 DL0 DR1 AR0 BL1 EL1 DL0 BL0,RWL 4 2)::
(makeTM BR0 HR1 CR1 DL0 DR1 AR1 BL1 EL0 ER1 CR0,RWL 3 3)::
(makeTM BR0 HR1 CR1 DL0 DR1 ER1 EL0 AR0 CL1 BL1,RWL 6 2)::
(makeTM BR0 HR1 CR1 DR0 DL0 CL0 ER1 CL1 EL0 AR1,RWL 4 3)::
(makeTM BR0 HR1 CR1 DR0 DL1 AR0 EL0 DL1 BL1 DL0,RWL 17 2)::
(makeTM BR0 HR1 CR1 DR0 DL1 BL0 ER1 CL0 DL0 AR1,RWL 6 2)::
(makeTM BR0 HR1 CR1 DR0 DL1 BL1 ER1 CL0 CR0 AR1,RWL 8 2)::
(makeTM BR0 HR1 CR1 DR0 DL1 BL1 ER1 CL0 CR1 AR1,RWL 8 2)::
(makeTM BR0 HR1 CR1 DR0 DL1 CR0 EL0 EL1 BL1 AR0,RWL 1 4)::
(makeTM BR0 HR1 CR1 DR0 DL1 ER0 EL0 DL1 AR1 BL0,RWL 1 3)::
(makeTM BR0 HR1 CR1 DL1 DL1 CL0 EL0 BL1 ER1 AR0,RWL 2 2)::
(makeTM BR0 HR1 CR1 DR1 DL0 CL1 AR1 EL0 CL1 BR0,RWL 3 2)::
(makeTM BR0 HR1 CR1 EL0 DL0 CR0 BR1 DL1 AL0 BL1,RWL 4 3)::
(makeTM BR0 HR1 CR1 EL0 DL0 CR0 BR1 DL1 ER0 BL1,RWL 2 3)::
(makeTM BR0 HR1 CR1 EL0 DL0 ER0 BL1 CL0 DL1 AR0,RWL 2 2)::
(makeTM BR0 HR1 CR1 EL0 DL0 ER0 BL1 CL1 DL1 AR0,RWL 4 3)::
(makeTM BR0 HR1 CR1 EL0 DR0 BL0 BL1 AR1 CL1 DL0,RWL 16 2)::
(makeTM BR0 HR1 CR1 EL0 DR0 CR1 EL1 ER0 BL1 AR1,RWL 3 3)::
(makeTM BR0 HR1 CR1 EL0 DL1 AR0 BL1 DL0 BR1 AR1,RWL 28 2)::
(makeTM BR0 HR1 CR1 EL0 DL1 CR1 HR1 BL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 HR1 CR1 EL0 DL1 ER0 BL1 DL1 AR1 DL0,RWL 2 4)::
(makeTM BR0 HR1 CR1 EL0 DR1 AR0 BL1 DR1 DL0 CL0,RWL 3 3)::
(makeTM BR0 HR1 CR1 EL0 DR1 CL0 BL1 AR0 CR0 BL1,RWL 3 3)::
(makeTM BR0 HR1 CR1 EL0 DR1 CL0 BL1 AR1 CR1 DR0,RWL 4 2)::
(makeTM BR0 HR1 CR1 EL0 DR1 CR0 BL1 AR0 BL1 DL0,RWL 6 2)::
(makeTM BR0 HR1 CR1 EL0 DR1 CR0 BL1 DL1 CL1 AL1,RWL 4 2)::
(makeTM BR0 HR1 CR1 EL0 DR1 CR0 ER1 ER0 BL1 AR1,RWL 4 3)::
(makeTM BR0 HR1 CR1 EL0 DR1 ER1 BL1 CR1 AR1 DL0,RWL 3 2)::
(makeTM BR0 HR1 CR1 ER0 CL1 DL0 AR1 DL0 CL0 DR0,RWL 8 2)::
(makeTM BR0 HR1 CR1 ER0 CL1 DL0 AR1 ER1 CL0 DR0,RWL 8 2)::
(makeTM BR0 HR1 CR1 ER0 DR0 AR1 DL1 EL0 BL1 CL1,RWL 5 2)::
(makeTM BR0 HR1 CR1 ER0 DR0 CL0 EL0 DR1 CL1 AR1,RWL 8 2)::
(makeTM BR0 HR1 CR1 ER0 DL1 AR1 ER0 CL0 BL0 BR1,RWL 14 2)::
(makeTM BR0 HR1 CR1 ER0 DL1 DR0 BR0 EL0 CL1 AR1,RWL 3 3)::
(makeTM BR0 HR1 CR1 ER0 DL1 ER1 AR1 DL0 EL1 DR1,RWL 15 2)::
(makeTM BR0 HR1 CR1 ER0 DR1 BR0 EL0 DL1 AR1 DL0,RWL 6 4)::
(makeTM BR0 HR1 CR1 ER0 DR1 CR0 EL0 DL1 AR1 DL0,RWL 3 3)::
(makeTM BR0 HR1 CR1 ER0 DR1 ER0 EL0 DL1 AR1 DL0,RWL 3 4)::
(makeTM BR0 HR1 CR1 EL1 DL1 AR0 BL1 DL0 BR1 ER1,RWL 6 2)::
(makeTM BR0 HR1 CR1 EL1 DL1 ER0 BR1 BL1 AL0 DL0,RWL 6 3)::
(makeTM BR0 HR1 CR1 ER1 DL1 AR0 BL1 DL0 BR1 EL0,RWL 3 3)::
(makeTM BR0 HR1 CR1 ER1 DL1 BL0 EL0 DL0 AR1 CR0,RWL 3 2)::
(makeTM BR0 HR1 CR1 ER1 DL1 CL0 BR1 BL1 AR0 BR0,RWL 3 3)::
(makeTM BR0 HR1 CR1 ER1 DL1 DL0 EL0 CL1 AR1 BR0,RWL 2 2)::
(makeTM BR0 HR1 CR1 ER1 DR1 CR1 BL0 AR1 EL1 DL0,RWL 9 2)::
(makeTM BR0 HR1 CR1 ER1 DR1 DR0 BL0 AR1 EL1 DL0,RWL 9 2)::
(makeTM BR0 AL0 AL1 CL1 DL0 CR0 ER1 EL0 BR1 HR1,RWL 12 2)::
(makeTM BR0 AL0 CL0 AR1 BR1 DL0 CL1 ER1 AR0 HR1,RWL 4 2)::
(makeTM BR0 AL0 CL0 DR0 AL1 EL1 BR1 AR1 BL1 HR1,RWL 4 2)::
(makeTM BR0 AL0 CL0 DR0 DR1 AL1 ER1 HR1 BR1 CL0,RWL 3 3)::
(makeTM BR0 AL0 CL0 DR1 AL1 EL1 ER1 HR1 BR1 AR0,RWL 3 2)::
(makeTM BR0 AL0 CL0 DR1 DR0 BL1 BR1 ER0 AR1 HR1,RWL 7 2)::
(makeTM BR0 AL0 CL0 DR1 DL1 HR1 EL1 DR0 AL1 BL0,RWL 4 2)::
(makeTM BR0 AL0 CL0 ER0 DL1 HR1 AL1 BL0 AR0 ER1,RWL 7 2)::
(makeTM BR0 AL0 CL0 ER0 DL1 AL1 BR1 DR1 AR1 HR1,RWL 10 2)::
(makeTM BR0 AL0 CR0 HR1 DR1 CL1 ER0 AR1 EL1 CL0,RWL 2 3)::
(makeTM BR0 AL0 CL1 HR1 DR1 AR0 EL1 CR0 AR1 DL1,RWL 2 2)::
(makeTM BR0 AL0 CL1 HR1 DR1 ER1 AL1 ER0 DL1 CR1,RWL 3 3)::
(makeTM BR0 AL0 CL1 AR0 DL0 AR1 ER1 CL0 DR1 HR1,RWL 2 3)::
(makeTM BR0 AL0 CL1 AL1 DR1 ER0 BL1 BR1 HR1 CR1,RWL 5 3)::
(makeTM BR0 AL0 CL1 AR1 DL0 HR1 EL1 DL1 BR1 ER0,RWL 9 2)::
(makeTM BR0 AL0 CL1 BR1 AL1 DR0 HR1 ER1 AL1 CR0,RWL 3 3)::
(makeTM BR0 AL0 CL1 BR1 AL1 DR0 HR1 ER1 BR0 CR0,RWL 6 2)::
(makeTM BR0 AL0 CL1 BR1 AL1 DR0 HR1 ER1 CR1 BL1,RWL 3 3)::
(makeTM BR0 AL0 CL1 BR1 AL1 DR0 HR1 ER1 CR1 BR1,RWL 3 3)::
(makeTM BR0 AL0 CL1 CR1 AL1 DR1 ER1 BL1 CR0 HR1,RWL 4 2)::
(makeTM BR0 AL0 CL1 CR1 AL1 DR1 ER1 DR1 CR0 HR1,RWL 4 2)::
(makeTM BR0 AL0 CL1 CR1 DR1 EL1 AL1 DR0 HR1 CL0,RWL 2 3)::
(makeTM BR0 AL0 CL1 DR0 DL0 AR1 AR1 EL1 BL0 HR1,RWL 6 2)::
(makeTM BR0 AL0 CL1 DR0 DL1 EL0 BR1 AR1 AL0 HR1,RWL 3 3)::
(makeTM BR0 AL0 CL1 DR0 DL1 EL0 BR1 AR1 CR1 HR1,RWL 3 3)::
(makeTM BR0 AL0 CL1 DR0 DL1 EL1 BR1 AR1 AR1 HR1,RWL 3 3)::
(makeTM BR0 AL0 CL1 DR0 DL1 EL1 BR1 AR1 BL1 HR1,RWL 6 2)::
(makeTM BR0 AL0 CL1 DR0 DR1 AR1 EL1 CR0 HR1 BL1,RWL 20 2)::
(makeTM BR0 AL0 CL1 DL1 DR1 AR1 EL1 CR0 HR1 BL1,RWL 6 2)::
(makeTM BR0 AL0 CL1 DR1 AL1 ER1 AR1 BR1 HR1 CR0,RWL 2 4)::
(makeTM BR0 AL0 CL1 EL0 DR1 AR1 BL1 CR0 DR0 HR1,RWL 5 3)::
(makeTM BR0 AL0 CL1 ER0 DL1 HR1 AL1 BL1 AR0 ER1,RWL 15 2)::
(makeTM BR0 AL0 CL1 ER0 DR1 AR1 BL1 CR0 HR1 DL1,RWL 5 3)::
(makeTM BR0 AL0 CL1 ER0 DR1 AR1 EL1 CR0 HR1 BL1,RWL 19 2)::
(makeTM BR0 AL0 CR1 HR1 DL1 AR0 ER0 DL0 CL1 ER1,RWL 4 3)::
(makeTM BR0 AL0 CR1 HR1 DL1 ER1 EL0 BL1 AL0 CR0,RWL 2 3)::
(makeTM BR0 AL0 CR1 HR1 DR1 EL0 CL1 CR0 AL1 CL1,RWL 2 3)::
(makeTM BR0 AL0 CR1 AR1 DL1 BR0 BL1 EL0 CL0 HR1,RWL 4 2)::
(makeTM BR0 AL0 CR1 BL0 DL0 AR0 BL1 EL1 CL1 HR1,RWL 5 2)::
(makeTM BR0 AL0 CR1 CL0 DL0 ER0 BL1 CL1 AR0 HR1,RWL 7 2)::
(makeTM BR0 AL0 CR1 DL0 BL1 EL0 CL0 HR1 AR1 ER0,RWL 3 2)::
(makeTM BR0 AL0 CR1 DL0 CL1 BL1 DR1 EL1 HR1 AR0,RWL 2 3)::
(makeTM BR0 AL0 CR1 DR1 AL1 CL1 AR1 EL1 HR1 DL0,RWL 15 2)::
(makeTM BR0 AL0 CR1 DR1 DL1 HR1 AR1 EL1 AL1 DL0,RWL 15 2)::
(makeTM BR0 AL0 CR1 ER1 DL0 CR1 AL1 DL1 HR1 BR0,RWL 2 2)::
(makeTM BR0 AL0 CR1 ER1 DR1 BR1 AL1 DL1 HR1 AR0,RWL 4 2)::
(makeTM BR0 AR0 CL0 DR0 DL1 EL0 BR1 AR1 CL1 HR1,RWL 4 2)::
(makeTM BR0 AR0 CR0 DR1 DL1 HR1 EL0 ER0 AR1 CL1,RWL 7 2)::
(makeTM BR0 AR0 CL1 AR1 DL0 HR1 EL0 DL0 ER1 BL1,RWL 2 3)::
(makeTM BR0 AR0 CL1 CR0 DL0 DL1 AR1 EL0 CL1 HR1,RWL 12 2)::
(makeTM BR0 AR0 CL1 EL0 DL0 HR1 AR1 BL0 DR1 BL1,RWL 4 3)::
(makeTM BR0 AR0 CL1 EL0 DL0 DL1 AR1 BL0 DR0 HR1,RWL 12 2)::
(makeTM BR0 AR0 CL1 EL1 DL0 HR1 EL1 DL1 AR1 CL0,RWL 8 2)::
(makeTM BR0 AR0 CR1 BL0 DR1 AR1 EL1 HR1 BL1 EL0,RWL 28 2)::
(makeTM BR0 AR0 CR1 CL0 DL1 AR1 EL0 CL1 BL1 HR1,RWL 4 2)::
(makeTM BR0 AR0 CR1 CL1 DL1 HR1 ER1 EL0 AL1 AR1,RWL 4 2)::
(makeTM BR0 AR0 CR1 DL0 DR1 ER0 BL1 AL1 AR1 HR1,RWL 9 4)::
(makeTM BR0 AR0 CR1 EL0 DR1 AR1 EL1 HR1 BL1 BL0,RWL 28 2)::
(makeTM BR0 AL1 CL0 BR1 DR1 CL1 AL1 ER1 HR1 BR0,RWL 2 2)::
(makeTM BR0 AL1 CL0 CR0 DR1 AL0 ER0 HR1 EL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL0 CR0 DR1 CL0 ER0 HR1 EL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL0 CR0 DR1 DL1 ER0 HR1 EL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL0 CR1 DR1 ER0 BL1 HR1 EL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL0 CR1 DR1 ER0 ER0 HR1 EL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL0 DL1 DL1 HR1 ER0 BL0 AR1 ER1,RWL 2 2)::
(makeTM BR0 AL1 CR0 BL1 DL1 CR1 AR1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 AL1 CR0 BR1 DL1 HR1 EL1 AL0 AR0 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR0 BR1 DL1 HR1 EL1 AL0 BR0 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR0 BR1 DL1 AL0 EL1 HR1 AR0 CL0,RWL 2 2)::
(makeTM BR0 AL1 CR0 BR1 DL1 AL0 EL1 HR1 BR0 CL0,RWL 2 2)::
(makeTM BR0 AL1 CR0 DL0 DR1 AR1 CL1 ER1 BR1 HR1,RWL 1 3)::
(makeTM BR0 AL1 CR0 DL1 DR1 HR1 BL0 ER1 AL1 AR0,RWL 13 2)::
(makeTM BR0 AL1 CL1 AL0 DR1 ER1 HR1 ER0 BL1 CR1,RWL 4 3)::
(makeTM BR0 AL1 CL1 BL0 DR1 EL0 AL0 CR1 HR1 AR0,RWL 3 3)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 AL0 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 AL0 EL0 HR1 DR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 AL0 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 AL0 EL1 HR1 CR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 AL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 AL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 AR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 AR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 BL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 BR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 BR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 CL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 CL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 DR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR0 DL1 ER1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL0 HR1 ER1 EL1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL0 EL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 AL1 DR0 EL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 AL0 HR1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL0 BR0 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL0 CR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL0 ER1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 ER0 AL0 EL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL1 AL0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL1 AL0 DR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL1 AR0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL1 BR0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL1 BL1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL1 CL1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AL1 DL1 HR1 EL1 DR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL0 HR1 ER1 EL1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL0 ER0 DL1 HR1 CL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL0 EL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 AR1 DR0 EL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 AL0 HR1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL0 BR0 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL0 CR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL0 ER1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 ER0 AL0 EL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL1 AL0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL1 AL0 DR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL1 AR0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL1 BR0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL1 BL1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL1 CL0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL1 CL1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 HR1 EL1 DR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 AR1 DL1 EL0 ER0 HR1 CL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 AL0 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 AL0 EL0 HR1 DR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 AL0 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 AL0 EL1 HR1 CR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 AL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 AL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 AR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 AR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 BL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 BR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 BR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 CL0 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 CL0 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 CL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 CL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 DR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR0 DL1 ER1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL0 HR1 ER1 EL1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL0 EL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DR0 EL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 AL0 HR1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL0 BR0 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL0 CR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL0 ER1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 ER0 AL0 EL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL1 AL0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL1 AL0 DR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL1 AR0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL1 BR0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL1 BL1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL1 CL1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 BR1 DL1 HR1 EL1 DR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 CR1 DL1 HR1 EL1 AR0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 CR1 DL1 HR1 EL1 AL1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 CR1 DL1 HR1 EL1 AR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 CR1 DL1 HR1 EL1 BR0 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 CR1 DL1 HR1 EL1 BR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 DL1 AL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 DL1 AR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 DL1 BR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 DL1 ER0 AL0 AL1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 DL1 ER0 AL0 AR1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 DL1 ER0 AL0 BR1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 AR1 HR1 AL0 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 AR1 HR1 AL0 CR0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 AR1 HR1 AL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 AR1 HR1 AR1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 AR1 HR1 BL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 AR1 HR1 BR1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 AR1 HR1 CL1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 AR1 HR1 CR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL0 EL1 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 AL0 HR1 ER1 AL1 DR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 AL0 HR1 ER1 BL1 DR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 AL0 HR1 ER1 BR1 DR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 HR1 AL1 AL0 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 HR1 AL1 AL1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 HR1 AL1 AR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 HR1 AL1 BR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 HR1 AL1 CL1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 HR1 AL1 DR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 AL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 AL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 AR1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 BL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 BR1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR0 EL1 BR1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DR0 EL0 AL0 AR1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DL1 AL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DL1 AL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DL1 AR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DL1 AR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DL1 BR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DL1 BR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DL1 EL0 AL0 AR1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 DL1 ER1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL0 AR0 AL0 HR1 BR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL0 AR0 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL0 AL1 AL0 HR1 BR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL0 AR1 AL0 HR1 BR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL0 BR0 AL0 HR1 BR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL0 BR0 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL0 BR1 AL0 HR1 BR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 ER0 AL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 ER0 AR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 ER0 BR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 AR0 HR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 AR0 AL0 HR1 DR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 AR0 AL0 HR1 DL1,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 AL1 AL0 HR1 DR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 AL1 AL0 HR1 DL1,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 AR1 AL0 HR1 DR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 AR1 AL0 HR1 DL1,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 BR0 HR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 BR0 AL0 HR1 DR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 BR0 AL0 HR1 DL1,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 BR0 AL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 BR1 AL0 HR1 DR0,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 BR1 AL0 HR1 DL1,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 CR1 AL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 DR0 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 DR0 AR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DL1 EL1 DR0 BR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 AL0 HR1 ER1 AL0 CR0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DR1 AL0 HR1 ER1 AL0 DR1,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DR1 AL0 HR1 ER1 BL0 CR0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DR1 AL0 HR1 ER1 BL0 DR1,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DR1 AL0 HR1 ER1 CL1 CR0,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DR1 AL0 HR1 ER1 CL1 DR1,RWL 2 3)::
(makeTM BR0 AL1 CL1 BR1 DR1 DL1 AL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 DL1 AR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 DL1 BR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 DL1 EL0 AL0 AR1 HR1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 DL1 ER1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL0 AL1 CR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL0 BL1 CR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL0 BR1 CR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL0 DL1 CR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL0 EL0 CR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 HR1 AL0 AL1 DL1,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 HR1 AL0 AR1 DL1,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 HR1 AL0 BR1 DL1,RWL 3 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 HR1 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 HR1 BL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 HR1 BR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 AL0 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 AR0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 BL0 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 BR0 AL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 BR0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 CL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 CR1 AL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 BR1 DR1 EL1 DR1 AL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 CR0 DL0 DL1 BR1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 AL1 CL1 CR1 DL1 CR1 AR0 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 CR1 DL1 CR1 BR0 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 CR1 DL1 CR1 CR0 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 DL0 BR1 EL1 CR0 CR1 HR1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 DL0 DL1 CR1 CR0 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 DL0 DR1 HR1 CR0 ER0 EL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 DR0 BR1 HR1 EL1 ER0 AL0 BL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 DR0 BR1 EL0 CR0 AL0 DL0 HR1,RWL 2 3)::
(makeTM BR0 AL1 CL1 DR0 BR1 EL0 CR1 AL0 HR1 DL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 DR0 BR1 EL1 CL0 AL0 HR1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 DR0 BR1 EL1 CL0 CL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 DR0 BR1 EL1 DL1 CL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 DR0 DL1 HR1 BR1 ER0 EL1 AL0,RWL 1 3)::
(makeTM BR0 AL1 CL1 DL1 DL1 CR1 CR0 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 DL1 DR1 HR1 ER0 BL0 AR1 ER1,RWL 2 2)::
(makeTM BR0 AL1 CL1 DR1 AL1 EL1 CL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 DR1 AR1 CL0 ER0 BR1 CR1 HR1,RWL 11 2)::
(makeTM BR0 AL1 CL1 DR1 AR1 EL1 CL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 DR1 BR1 EL1 CL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 DR1 CR1 BL1 HR1 ER0 EL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 DR1 DR1 HR1 HR1 ER0 EL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 DR1 DR1 AL0 HR1 ER0 BL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 DR1 DR1 AL0 HR1 ER0 BL1 CL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 DR1 DR1 EL1 HR1 ER0 BL1 AL0,RWL 3 3)::
(makeTM BR0 AL1 CL1 DR1 DR1 EL1 CL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 ER0 CR1 DR0 DL1 AL0 HR1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CL1 ER0 CR1 DR0 DL1 AL0 HR1 CL1,RWL 2 3)::
(makeTM BR0 AL1 CL1 ER0 DL1 CR1 CR0 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 ER0 DR1 AL0 EL1 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR0 AL1 CL1 ER0 DR1 EL1 CL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CL1 ER1 CR1 DR0 DL1 AL0 HR1 CL1,RWL 2 3)::
(makeTM BR0 AL1 CL1 ER1 CR1 DR0 DL1 AL0 HR1 DR0,RWL 2 3)::
(makeTM BR0 AL1 CL1 ER1 DL1 CR1 AL1 AL0 HR1 CR0,RWL 6 3)::
(makeTM BR0 AL1 CL1 ER1 DL1 CR1 AR1 AL0 HR1 CR0,RWL 6 3)::
(makeTM BR0 AL1 CL1 ER1 DL1 CR1 CR1 AL0 HR1 CR0,RWL 6 3)::
(makeTM BR0 AL1 CL1 ER1 DL1 CR1 ER1 AL0 HR1 CR0,RWL 6 3)::
(makeTM BR0 AL1 CR1 BL0 DR0 HR1 EL1 DR1 AL1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CR1 BL0 DR0 HR1 EL1 DR1 AR1 AL0,RWL 2 3)::
(makeTM BR0 AL1 CR1 BL1 AL1 DR0 EL1 DR1 HR1 BL0,RWL 2 3)::
(makeTM BR0 AL1 CR1 BL1 AL1 DR1 HR1 ER0 BL0 ER1,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 CL1 DL1 AR0 EL0 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 CL1 DL1 BR0 EL0 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 CL1 DR1 AL0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 CL1 DR1 AL1 EL1 HR1 DL0,RWL 4 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 AL0 HR1 EL1 BL1 DL1,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 AL1 HR1 EL0 BL1 DL1,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 AL1 HR1 EL1 AL0 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 AL1 HR1 EL1 AL1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 AL1 HR1 EL1 AR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 AL1 HR1 EL1 BR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 AL1 HR1 EL1 CR1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 AR1 HR1 EL1 AL1 CL0,RWL 3 3)::
(makeTM BR0 AL1 CR1 BR1 DL0 AR1 HR1 EL1 AR1 CL0,RWL 3 3)::
(makeTM BR0 AL1 CR1 BR1 DL0 ER1 HR1 EL1 AL0 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL0 ER1 BL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL0 HR1 EL1 AL0 CL0,RWL 2 3)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL0 HR1 EL1 AL0 DL1,RWL 2 3)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL0 HR1 EL1 AR0 CL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL0 HR1 EL1 BR0 CL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL0 HR1 EL1 CR1 CL0,RWL 2 3)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL0 HR1 EL1 CR1 DL1,RWL 2 3)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL1 HR1 EL0 BR0 DL1,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL1 HR1 EL0 BL1 DL1,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL1 HR1 EL1 AR0 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL1 HR1 EL1 BR0 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL1 HR1 EL1 BL1 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL1 HR1 EL1 CR0 DL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 EL0 AL1 CL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 EL0 AR1 CL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 EL0 BR1 CL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 ER1 HR1 EL0 AL1 DL1,RWL 4 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 ER1 AL0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 ER1 CR1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 CR0 DL1 AL0 EL1 BL1 BR1 HR1,RWL 1 3)::
(makeTM BR0 AL1 CR1 CR0 DL1 AL0 EL1 CL1 BR1 HR1,RWL 1 3)::
(makeTM BR0 AL1 CR1 DR0 DL1 HR1 BL0 EL1 BR1 AL0,RWL 2 2)::
(makeTM BR0 AL1 CR1 DL1 DR1 CR0 AL0 EL0 HR1 BL0,RWL 2 3)::
(makeTM BR0 AR1 AL1 CR1 DL1 EL0 AR0 CL1 HR1 DL1,RWL 6 4)::
(makeTM BR0 AR1 CL0 AR0 DL0 HR1 ER1 DL1 AL1 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL0 AR0 DL0 HR1 ER1 DL1 AR1 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL0 AR0 DL0 HR1 ER1 DL1 CR1 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL0 AR0 DL0 HR1 ER1 DL1 DL1 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL0 BR1 DL1 CL1 AR1 EL1 HR1 BR0,RWL 2 2)::
(makeTM BR0 AR1 CL0 BR1 DR1 CL1 BL1 ER1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AR1 CL0 BR1 DR1 CL1 BR1 ER1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AR1 CL0 BR1 DR1 CL1 CL1 ER1 HR1 AL0,RWL 2 2)::
(makeTM BR0 AR1 CL0 CR1 DL1 EL1 AR0 CL1 HR1 BL0,RWL 3 3)::
(makeTM BR0 AR1 CL0 DR0 DR1 EL1 ER0 HR1 BL1 AL0,RWL 3 2)::
(makeTM BR0 AR1 CL0 EL0 DL1 HR1 EL1 DL0 AR0 BL1,RWL 6 2)::
(makeTM BR0 AR1 CL0 ER0 DL0 HR1 AL1 DL1 DR1 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL0 ER0 DL1 BL1 AR0 CL1 HR1 DR1,RWL 7 2)::
(makeTM BR0 AR1 CL0 ER1 DR1 CL1 BL1 AL0 HR1 DR0,RWL 2 3)::
(makeTM BR0 AR1 CR0 BL0 DL0 AR0 EL1 HR1 BL1 CL0,RWL 7 2)::
(makeTM BR0 AR1 CR0 BL0 DL1 AR0 EL1 HR1 BL1 CL1,RWL 15 2)::
(makeTM BR0 AR1 CR0 CL1 DL1 DR1 CR1 EL0 HR1 AL1,RWL 1 4)::
(makeTM BR0 AR1 CL1 HR1 DL1 EL0 AR0 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR0 AR1 CL1 HR1 DL1 EL0 ER0 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR0 AR1 CL1 AR0 DL0 AR1 ER1 CL0 DR1 HR1,RWL 2 3)::
(makeTM BR0 AR1 CL1 BL0 DL1 AR0 ER1 BL1 HR1 DR0,RWL 18 2)::
(makeTM BR0 AR1 CL1 BL0 DL1 CL1 AR0 EL0 HR1 AL0,RWL 2 2)::
(makeTM BR0 AR1 CL1 BL0 DL1 ER0 CR0 BL1 HR1 AR1,RWL 12 2)::
(makeTM BR0 AR1 CL1 BR0 DL1 BL0 EL1 CL0 AR1 HR1,RWL 3 3)::
(makeTM BR0 AR1 CL1 BL1 DL1 BL1 AR0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR0 AR1 CL1 BL1 DL1 BR1 AR0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR0 AR1 CL1 BL1 DR1 AR1 HR1 ER1 BL0 DR0,RWL 2 2)::
(makeTM BR0 AR1 CL1 BR1 BR1 DL0 ER1 DL1 HR1 AL0,RWL 2 3)::
(makeTM BR0 AR1 CL1 BR1 DL0 AR1 ER1 CL0 DR1 HR1,RWL 4 2)::
(makeTM BR0 AR1 CL1 BR1 DL1 EL0 AR1 CL0 HR1 BR0,RWL 6 2)::
(makeTM BR0 AR1 CL1 BR1 DL1 EL1 AR1 CL0 HR1 DL1,RWL 6 2)::
(makeTM BR0 AR1 CL1 CR0 DR1 ER1 AL1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR0 AR1 CL1 CR1 DL1 AL1 ER1 CL0 HR1 DR1,RWL 6 2)::
(makeTM BR0 AR1 CL1 CR1 DL1 ER0 AL1 DL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 AR1 CL1 CR1 DL1 ER0 AL1 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR0 AR1 CL1 CR1 DL1 ER1 AL1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR0 AR1 CL1 DL0 DL1 HR1 AR0 EL0 BR0 BL1,RWL 5 2)::
(makeTM BR0 AR1 CL1 DR0 DL0 HR1 EL1 AL0 AR1 BL0,RWL 1 3)::
(makeTM BR0 AR1 CL1 DR0 DL0 CL0 AR1 ER0 BL0 HR1,RWL 6 2)::
(makeTM BR0 AR1 CL1 DR0 DL1 BL0 ER1 CL1 HR1 AR0,RWL 24 2)::
(makeTM BR0 AR1 CL1 DR0 DL1 BL1 ER1 BL0 HR1 AR0,RWL 11 2)::
(makeTM BR0 AR1 CL1 DR1 DL0 HR1 ER1 AL0 AR0 CR0,RWL 10 2)::
(makeTM BR0 AR1 CL1 DR1 DL0 BL1 AL1 EL1 HR1 CL0,RWL 3 2)::
(makeTM BR0 AR1 CL1 EL0 DL0 HR1 ER0 BL1 AR0 BL0,RWL 6 2)::
(makeTM BR0 AR1 CL1 EL0 DL1 HR1 AR0 BL0 AR0 EL1,RWL 2 2)::
(makeTM BR0 AR1 CL1 EL0 DL1 HR1 ER0 BL0 AR0 EL1,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER0 DL0 HR1 AL1 BL1 AR1 DL0,RWL 3 2)::
(makeTM BR0 AR1 CL1 ER0 DL1 HR1 AL1 DL1 BR0 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER0 DL1 HR1 AL1 DL1 CR1 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER0 DL1 HR1 AL1 DL1 DL0 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER0 DL1 HR1 AL1 DL1 DR1 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER0 DL1 CL0 AR0 CL1 HR1 CR0,RWL 15 2)::
(makeTM BR0 AR1 CL1 ER0 DR1 HR1 AL1 DL1 BR0 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER0 DR1 HR1 AL1 DL1 DL0 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER0 DR1 HR1 AL1 DL1 DR1 BR1,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER1 CR1 DL0 DR1 BR1 HR1 AR0,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER1 DL0 DL0 DR1 BR1 HR1 AR0,RWL 2 2)::
(makeTM BR0 AR1 CL1 ER1 DL1 CL0 AR0 AL0 HR1 CR0,RWL 7 2)::
(makeTM BR0 AR1 CR1 AL0 DL1 EL0 AR0 CL1 HR1 DL1,RWL 6 4)::
(makeTM BR0 AR1 CR1 AR0 DL1 AL0 AR1 EL0 CL0 HR1,RWL 17 2)::
(makeTM BR0 AR1 CR1 CL0 DL0 AL1 HR1 EL1 BL1 EL1,RWL 5 3)::
(makeTM BR0 AR1 CR1 CR0 DL1 AL0 DL0 EL0 BL1 HR1,RWL 2 4)::
(makeTM BR0 AR1 CR1 CL1 DL1 ER0 HR1 EL0 BL1 AR1,RWL 1 3)::
(makeTM BR0 AR1 CR1 CR1 DL1 EL0 AR0 CL1 HR1 DL1,RWL 6 4)::
(makeTM BR0 AR1 CR1 DL0 BL1 ER1 BL1 DL0 AR0 HR1,RWL 8 3)::
(makeTM BR0 AR1 CR1 DL0 DL1 EL1 AR1 CL0 HR1 DL1,RWL 6 2)::
(makeTM BR0 AR1 CR1 DL0 DL1 ER1 BL1 DL0 AR0 HR1,RWL 8 3)::
(makeTM BR0 AR1 CR1 DR1 DL1 ER1 AL1 CL0 DR0 HR1,RWL 4 3)::
(makeTM BR0 AR1 CR1 EL0 DL0 AR0 BL1 DL1 CL1 HR1,RWL 7 2)::
(makeTM BR0 AR1 CR1 EL1 DR0 HR1 DL1 BL0 AR0 BL0,RWL 8 2)::
(makeTM BR0 BL0 CL0 ER0 DL1 HR1 EL0 BL1 AR1 DL0,RWL 15 2)::
(makeTM BR0 BL0 CR0 BL1 DL1 CR1 AL1 EL0 HR1 CR0,RWL 3 2)::
(makeTM BR0 BL0 CR0 BL1 DL1 CR1 AL1 EL0 HR1 DR1,RWL 2 2)::
(makeTM BR0 BL0 CR0 BL1 DL1 CR1 AL1 EL1 HR1 AR0,RWL 3 2)::
(makeTM BR0 BL0 CR0 BL1 DL1 CR1 AL1 EL1 HR1 AL1,RWL 3 2)::
(makeTM BR0 BL0 CR0 BL1 DL1 CR1 BL1 EL1 HR1 AL1,RWL 3 2)::
(makeTM BR0 BL0 CR0 BL1 DL1 CR1 BR1 EL1 HR1 AL1,RWL 3 2)::
(makeTM BR0 BL0 CR0 BL1 DL1 CR1 CR1 EL1 HR1 AL1,RWL 3 2)::
(makeTM BR0 BL0 CR0 BL1 DL1 CR1 DR1 EL1 HR1 AL1,RWL 3 2)::
(makeTM BR0 BL0 CR0 BR1 DL1 ER1 AL1 DL0 HR1 DR0,RWL 7 2)::
(makeTM BR0 BL0 CL1 BR0 DL0 HR1 DR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR0 BL0 CL1 BL1 CR1 DR0 DL1 ER1 HR1 AR1,RWL 4 3)::
(makeTM BR0 BL0 CL1 BR1 DL0 CR0 EL1 EL0 AL1 HR1,RWL 5 2)::
(makeTM BR0 BL0 CL1 CR1 BR1 DR1 HR1 ER0 EL1 AR0,RWL 5 2)::
(makeTM BR0 BL0 CL1 CR1 DL0 HR1 DR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR0 BL0 CL1 CR1 DL1 CR0 EL0 EL1 AL1 HR1,RWL 10 2)::
(makeTM BR0 BL0 CL1 DL0 AL1 ER0 EL1 HR1 CR1 BR0,RWL 5 2)::
(makeTM BR0 BL0 CL1 DR0 AL1 EL1 CR1 DR1 HR1 AL0,RWL 1 3)::
(makeTM BR0 BL0 CL1 DR1 AR1 EL1 BR1 EL0 HR1 CL0,RWL 2 3)::
(makeTM BR0 BL0 CL1 EL0 DL1 AL0 AR1 HR1 ER1 AR0,RWL 8 2)::
(makeTM BR0 BL0 CL1 ER0 DL0 HR1 DR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR0 BL0 CL1 ER0 DL1 DR1 AR1 BL0 CR1 HR1,RWL 5 2)::
(makeTM BR0 BL0 CL1 EL1 DR1 AL0 BR1 CR0 HR1 CL1,RWL 4 2)::
(makeTM BR0 BL0 CL1 ER1 DL0 CL0 DR1 AL1 AR1 HR1,RWL 7 2)::
(makeTM BR0 BL0 CL1 ER1 DL0 CL0 EL0 AL1 AR1 HR1,RWL 7 2)::
(makeTM BR0 BL0 CR1 BL1 BL1 DR0 HR1 ER1 AL1 DR1,RWL 2 3)::
(makeTM BR0 BL0 CR1 BL1 BL1 DR0 HR1 ER1 AL1 ER1,RWL 2 3)::
(makeTM BR0 BL0 CR1 BL1 DL1 ER0 HR1 AL0 CL1 BR1,RWL 3 2)::
(makeTM BR0 BL0 CR1 BL1 DR1 EL1 AL1 DR0 HR1 CL0,RWL 5 2)::
(makeTM BR0 BL0 CR1 CL0 DL1 ER0 BR0 AL0 BR1 HR1,RWL 7 2)::
(makeTM BR0 BL0 CR1 DL0 BL1 ER0 ER1 AL1 AR1 HR1,RWL 8 2)::
(makeTM BR0 BL0 CR1 DR0 DR0 HR1 EL1 DR1 BL0 AL0,RWL 2 3)::
(makeTM BR0 BL0 CR1 DL1 DR0 CR1 AL1 ER0 HR1 CR0,RWL 15 2)::
(makeTM BR0 BL0 CR1 EL0 DR0 BR0 DL1 AL0 CR1 HR1,RWL 5 3)::
(makeTM BR0 BL0 CR1 EL1 DR0 BR0 DL1 AL0 AR0 HR1,RWL 5 3)::
(makeTM BR0 BL0 CR1 EL1 DR1 HR1 AL1 ER0 BL0 AR0,RWL 15 2)::
(makeTM BR0 BL0 CR1 ER1 DR0 HR1 EL1 DR1 AL1 AL0,RWL 2 3)::
(makeTM BR0 BR0 CL0 BR1 DR1 CL1 BL1 ER1 HR1 AR1,RWL 3 2)::
(makeTM BR0 BR0 CL0 BR1 DR1 CL1 BR1 ER1 HR1 AR1,RWL 3 2)::
(makeTM BR0 BR0 CL0 BR1 DR1 CL1 CL1 ER1 HR1 AR1,RWL 3 2)::
(makeTM BR0 BR0 CL0 BR1 DR1 CL1 ER0 AR1 BL1 HR1,RWL 2 2)::
(makeTM BR0 BR0 CL1 AL0 DL0 HR1 DR1 ER0 AL1 BR1,RWL 2 2)::
(makeTM BR0 BR0 CL1 BR1 BR1 DL0 HR1 EL1 AR1 DL1,RWL 2 3)::
(makeTM BR0 BR0 CL1 BR1 BR1 DL0 HR1 EL1 AR1 EL1,RWL 2 3)::
(makeTM BR0 BR0 CR1 CL1 BL1 DL1 HR1 EL0 ER1 AL0,RWL 5 2)::
(makeTM BR0 BR0 CR1 DL0 DR1 ER1 BL1 AL1 CR0 HR1,RWL 6 2)::
(makeTM BR0 BL1 AL1 CL1 BR1 DL0 DR1 EL0 HR1 CR0,RWL 5 2)::
(makeTM BR0 BL1 CL0 DR1 AL1 ER0 CR1 AL0 BR1 HR1,RWL 5 2)::
(makeTM BR0 BL1 CL0 DR1 DL1 CL1 AR1 EL0 HR1 AL1,RWL 6 2)::
(makeTM BR0 BL1 CL0 ER1 DL1 HR1 EL1 BR0 AL1 ER0,RWL 5 2)::
(makeTM BR0 BL1 CL0 ER1 DL1 AL1 EL0 HR1 BR1 CR0,RWL 6 3)::
(makeTM BR0 BL1 CR0 BL1 DL1 CR1 AR1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 BL1 CL1 HR1 DL1 EL1 ER1 CL0 AL1 DR0,RWL 4 2)::
(makeTM BR0 BL1 CL1 HR1 DR1 AL0 AL1 ER0 DL0 CR0,RWL 4 2)::
(makeTM BR0 BL1 CL1 HR1 DR1 ER0 AL1 CR0 EL1 BL0,RWL 14 2)::
(makeTM BR0 BL1 CL1 AL0 DR1 EL1 AL0 CR0 BL0 HR1,RWL 14 2)::
(makeTM BR0 BL1 CL1 BL0 DR1 HR1 ER0 DR0 EL1 AR1,RWL 2 3)::
(makeTM BR0 BL1 CL1 BR1 AL1 DL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 BL1 CL1 BR1 AR1 DL0 ER0 DL1 HR1 CL0,RWL 2 3)::
(makeTM BR0 BL1 CL1 BR1 AR1 DL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 BL1 CL1 BR1 AR1 DL1 HR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 BL1 CL1 CL0 AR1 DL0 HR1 EL0 ER1 AR0,RWL 1 4)::
(makeTM BR0 BL1 CL1 CL0 AR1 DL1 ER1 AR0 HR1 DR0,RWL 2 4)::
(makeTM BR0 BL1 CL1 CL0 DR0 CL1 HR1 ER1 AL1 ER1,RWL 2 2)::
(makeTM BR0 BL1 CL1 CR0 AR1 DL0 EL1 HR1 BR1 AL0,RWL 4 2)::
(makeTM BR0 BL1 CL1 CR0 DL1 AR1 CR1 EL0 AL0 HR1,RWL 3 2)::
(makeTM BR0 BL1 CL1 CR1 BR1 DL0 HR1 EL1 AR0 ER1,RWL 1 4)::
(makeTM BR0 BL1 CL1 CR1 DL1 CR0 BR1 EL0 HR1 AL0,RWL 6 2)::
(makeTM BR0 BL1 CL1 DL0 AR1 HR1 DR1 ER0 AL0 BR1,RWL 2 2)::
(makeTM BR0 BL1 CL1 DL0 AR1 HR1 DR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR0 BL1 CL1 DL0 CR1 DR0 EL1 AR0 BL1 HR1,RWL 5 2)::
(makeTM BR0 BL1 CL1 DL0 DL0 HR1 DR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR0 BL1 CL1 DL0 DL1 HR1 ER0 AL0 BR0 ER1,RWL 5 2)::
(makeTM BR0 BL1 CL1 DL0 DL1 ER1 AR1 CL1 HR1 CR0,RWL 2 3)::
(makeTM BR0 BL1 CL1 DR0 AL1 HR1 AR1 EL1 DL0 EL1,RWL 5 2)::
(makeTM BR0 BL1 CL1 DR0 BR1 EL0 CR0 AL0 DL0 HR1,RWL 2 3)::
(makeTM BR0 BL1 CL1 DR0 BR1 EL0 CR1 AL0 HR1 DL0,RWL 2 3)::
(makeTM BR0 BL1 CL1 DR0 DL1 HR1 AR1 EL0 DR1 AL0,RWL 7 2)::
(makeTM BR0 BL1 CL1 DR0 DL1 ER0 CR1 AL0 HR1 AR1,RWL 5 2)::
(makeTM BR0 BL1 CL1 DL1 AL1 AR1 ER1 EL0 HR1 CL0,RWL 4 2)::
(makeTM BR0 BL1 CL1 DR1 AL1 BR0 EL1 CR1 HR1 DL0,RWL 3 2)::
(makeTM BR0 BL1 CL1 DR1 AR1 EL0 HR1 CL1 ER1 BR0,RWL 2 2)::
(makeTM BR0 BL1 CL1 EL0 DR0 AR0 AL1 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR0 BL1 CL1 EL0 DR0 CL1 AL1 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR0 BL1 CL1 ER0 DL1 DL0 BR1 AL0 HR1 DR0,RWL 1 4)::
(makeTM BR0 BL1 CL1 ER0 DL1 DR1 BR1 AL0 HR1 CR1,RWL 3 3)::
(makeTM BR0 BL1 CL1 ER0 DR1 AR1 AL1 CR0 HR1 BL0,RWL 29 2)::
(makeTM BR0 BL1 CL1 ER1 DL1 CR0 AR1 DL0 HR1 CR1,RWL 7 3)::
(makeTM BR0 BL1 CR1 HR1 DL1 CR0 EL0 EL1 AL0 CL1,RWL 10 2)::
(makeTM BR0 BL1 CR1 BL0 AL0 DR0 ER1 HR1 BL1 AR0,RWL 3 3)::
(makeTM BR0 BL1 CR1 BL1 AL1 DR0 EL1 DR1 HR1 BL0,RWL 2 3)::
(makeTM BR0 BL1 CR1 BL1 AL1 DR1 HR1 ER0 BL0 ER1,RWL 2 2)::
(makeTM BR0 BL1 CR1 CL1 DL1 ER0 HR1 AR0 EL1 BL0,RWL 2 2)::
(makeTM BR0 BL1 CR1 CL1 DR1 EL0 EL0 BR0 HR1 AL1,RWL 6 2)::
(makeTM BR0 BL1 CR1 DL0 AL1 CR1 HR1 EL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 BL1 CR1 DL0 AL1 CR1 ER0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 BL1 CR1 DL0 AL1 CR1 ER0 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR0 BL1 CR1 DL1 DL1 ER0 HR1 AR0 EL1 BL0,RWL 2 2)::
(makeTM BR0 BL1 CR1 ER0 AL1 DR1 ER0 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR0 BL1 CR1 ER1 DL0 BR1 AL0 DL1 HR1 AR0,RWL 3 3)::
(makeTM BR0 BR1 CL0 BR1 DR1 CL1 AL1 ER1 HR1 BR0,RWL 2 2)::
(makeTM BR0 BR1 CL0 DR1 DL1 BL0 AR1 EL0 HR1 CL1,RWL 4 2)::
(makeTM BR0 BR1 CL0 ER1 DL1 DR0 AR1 DL0 CR1 HR1,RWL 38 2)::
(makeTM BR0 BR1 CR0 DL0 AL1 ER1 EL1 HR1 AR1 EL0,RWL 12 2)::
(makeTM BR0 BR1 CR0 DL0 DR1 ER1 BL1 CL0 AR1 HR1,RWL 8 2)::
(makeTM BR0 BR1 CR0 ER1 DL0 DR1 EL1 HR1 AR1 EL0,RWL 10 2)::
(makeTM BR0 BR1 CL1 AR0 DL1 HR1 EL1 DL1 BR0 ER1,RWL 2 2)::
(makeTM BR0 BR1 CL1 AR0 DR1 HR1 EL1 DL1 BR0 ER1,RWL 2 2)::
(makeTM BR0 BR1 CL1 AR1 AR0 DL0 EL0 HR1 CR0 BL0,RWL 2 4)::
(makeTM BR0 BR1 CL1 AR1 DL0 AL1 ER1 CL0 DR1 HR1,RWL 2 2)::
(makeTM BR0 BR1 CL1 AR1 DL0 BR0 EL1 BL0 AL1 HR1,RWL 10 2)::
(makeTM BR0 BR1 CL1 AR1 DL0 BR0 EL1 BL0 AR1 HR1,RWL 10 2)::
(makeTM BR0 BR1 CL1 BR1 AL1 DL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 BR1 CL1 BR1 AR1 DL0 ER0 DL1 HR1 CL0,RWL 2 3)::
(makeTM BR0 BR1 CL1 BR1 AR1 DL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 BR1 CL1 BR1 AR1 DL1 HR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 BR1 CL1 CL0 DR0 AL0 EL1 DR1 HR1 BL1,RWL 2 3)::
(makeTM BR0 BR1 CL1 CL0 DL1 DR1 ER1 BL1 HR1 AR0,RWL 9 2)::
(makeTM BR0 BR1 CL1 CL0 DR1 AL0 HR1 ER0 BL1 ER1,RWL 2 3)::
(makeTM BR0 BR1 CL1 CR1 AR1 DL1 HR1 EL0 BL1 AR1,RWL 12 2)::
(makeTM BR0 BR1 CL1 CR1 DR1 EL0 HR1 AL0 ER1 BR0,RWL 2 2)::
(makeTM BR0 BR1 CL1 DL0 AL1 HR1 CR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR0 BR1 CL1 DL0 AL1 HR1 DR1 ER0 AL0 BR1,RWL 2 2)::
(makeTM BR0 BR1 CL1 DL0 AL1 HR1 EL0 AR1 ER1 AR0,RWL 3 2)::
(makeTM BR0 BR1 CL1 DL0 AL1 HR1 EL0 CR0 ER1 AR0,RWL 3 2)::
(makeTM BR0 BR1 CL1 DL0 AL1 HR1 EL0 DL1 ER1 AR0,RWL 3 2)::
(makeTM BR0 BR1 CL1 DL0 AL1 HR1 EL0 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR0 BR1 CL1 DL0 AL1 HR1 EL1 AR0 DR1 EL1,RWL 2 4)::
(makeTM BR0 BR1 CL1 DL0 DL0 HR1 CR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR0 BR1 CL1 DL0 DL0 HR1 EL1 AR0 DR1 EL1,RWL 2 4)::
(makeTM BR0 BR1 CL1 DL0 DL1 HR1 BR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR0 BR1 CL1 DR0 AL1 EL0 AR1 DL1 HR1 DL0,RWL 2 3)::
(makeTM BR0 BR1 CL1 DR0 AR1 AL0 HR1 ER1 CL0 ER1,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR0 AR1 AL0 EL0 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR0 AR1 AL0 EL0 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR0 AR1 CL1 HR1 ER1 CL0 ER1,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR0 AR1 CL1 EL0 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR0 AR1 CL1 EL0 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR0 DL0 CL0 AR1 ER0 BL0 HR1,RWL 12 2)::
(makeTM BR0 BR1 CL1 DR0 DR0 EL0 AR1 DL1 HR1 DL0,RWL 2 3)::
(makeTM BR0 BR1 CL1 DR0 DR1 EL0 HR1 AL0 ER1 BR0,RWL 2 2)::
(makeTM BR0 BR1 CL1 DL1 BR0 EL1 AR1 ER0 HR1 AL0,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR1 AL1 EL0 HR1 AL0 ER1 BR0,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR1 AL1 EL0 HR1 CL1 ER1 BR0,RWL 2 2)::
(makeTM BR0 BR1 CL1 DR1 AR1 AL0 HR1 ER0 CL0 ER1,RWL 3 2)::
(makeTM BR0 BR1 CL1 DR1 AR1 CL1 HR1 ER0 CL0 ER1,RWL 3 2)::
(makeTM BR0 BR1 CL1 DR1 DL0 HR1 EL0 AR1 ER1 BR0,RWL 4 2)::
(makeTM BR0 BR1 CL1 DR1 DR1 EL0 HR1 AL0 ER1 BR0,RWL 2 2)::
(makeTM BR0 BR1 CL1 EL0 DL0 HR1 AR1 DL1 AR1 AR0,RWL 2 3)::
(makeTM BR0 BR1 CL1 EL0 DL0 HR1 AR1 DL1 CR0 AR0,RWL 2 3)::
(makeTM BR0 BR1 CL1 ER0 DL0 CL0 AR1 AL0 AR1 HR1,RWL 12 2)::
(makeTM BR0 BR1 CL1 ER0 DL0 CR0 AR1 BL0 DL1 HR1,RWL 6 2)::
(makeTM BR0 BR1 CL1 ER0 DR1 AL0 HR1 BR1 CL0 ER1,RWL 2 2)::
(makeTM BR0 BR1 CL1 EL1 AR1 DL1 HR1 AL0 DR0 BR0,RWL 2 2)::
(makeTM BR0 BR1 CL1 ER1 AR1 DL1 HR1 CL0 BR1 DL0,RWL 2 3)::
(makeTM BR0 BR1 CL1 ER1 DL1 AL0 BR1 DR0 HR1 AR1,RWL 3 3)::
(makeTM BR0 BR1 CR1 HR1 DL0 DR0 ER1 EL1 AR1 EL0,RWL 10 2)::
(makeTM BR0 BR1 CR1 HR1 DL1 EL0 AR1 CL0 ER1 BR0,RWL 14 2)::
(makeTM BR0 BR1 CR1 BL0 DR1 DR0 EL1 AR0 HR1 BL1,RWL 8 3)::
(makeTM BR0 BR1 CR1 BL1 AL1 DR0 EL1 DR1 HR1 BL0,RWL 2 3)::
(makeTM BR0 BR1 CR1 BL1 AL1 DR1 HR1 ER0 BL0 ER1,RWL 2 2)::
(makeTM BR0 BR1 CR1 CR0 DL0 AL0 HR1 EL1 AR1 EL1,RWL 2 2)::
(makeTM BR0 BR1 CR1 CR0 DL0 AL0 ER1 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 BR1 CR1 CR0 DL0 CR1 HR1 EL1 AR1 EL1,RWL 2 2)::
(makeTM BR0 BR1 CR1 CR0 DL1 AL0 HR1 EL0 BR1 EL1,RWL 2 3)::
(makeTM BR0 BR1 CR1 CL1 DL1 ER0 HR1 AL0 EL1 BL0,RWL 2 3)::
(makeTM BR0 BR1 CR1 DL0 DL1 ER0 HR1 AL0 EL1 BL0,RWL 2 3)::
(makeTM BR0 BR1 CR1 DR0 AL1 HR1 DL1 EL0 AL0 BL1,RWL 2 2)::
(makeTM BR0 BR1 CR1 DL1 AL1 ER0 HR1 AL0 EL1 BL0,RWL 2 3)::
(makeTM BR0 BR1 CR1 DL1 AL1 ER0 HR1 CR1 EL1 BL0,RWL 2 2)::
(makeTM BR0 BR1 CR1 DL1 DL1 ER0 HR1 AL0 EL1 BL0,RWL 2 3)::
(makeTM BR0 BR1 CR1 EL0 DL1 AL0 HR1 BL1 CR0 EL1,RWL 2 3)::
(makeTM BR0 BR1 CR1 ER0 DL0 AL0 AR1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 BR1 CR1 ER0 DL0 AL0 AR1 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR0 BR1 CR1 ER0 DL0 CR1 AR1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 BR1 CR1 ER0 DL0 CR1 AR1 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR0 BR1 CR1 ER0 DL1 BL1 AR1 CL0 HR1 AL0,RWL 9 2)::
(makeTM BR0 BR1 CR1 ER1 DL0 AL0 AR1 DL1 HR1 CR0,RWL 3 2)::
(makeTM BR0 BR1 CR1 ER1 DL0 CR1 AR1 DL1 HR1 CR0,RWL 3 2)::
(makeTM BR0 CL0 AL1 BR1 BL1 DL1 ER1 BR0 HR1 DR1,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DL0 EL0 DR1 BR0 HR1 DL1,RWL 2 4)::
(makeTM BR0 CL0 AL1 BR1 DR1 CL1 BL1 ER0 HR1 AL0,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 CL1 BL1 ER0 HR1 AL1,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 CL1 BL1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 CL1 BR1 ER0 HR1 AL0,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 CL1 BR1 ER0 HR1 AL1,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 CL1 BR1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 CL1 EL1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 CL1 ER1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 EL1 BL1 BR0 HR1 CL1,RWL 2 3)::
(makeTM BR0 CL0 AL1 BR1 DR1 EL1 BR1 BR0 HR1 CL1,RWL 2 3)::
(makeTM BR0 CL0 AL1 CL1 DR1 BR0 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL0 AL1 CL1 DR1 ER0 HR1 BR1 BL1 AL0,RWL 2 2)::
(makeTM BR0 CL0 CL0 HR1 DR0 CL1 EL1 DR1 CL1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CL0 HR1 DR0 CL1 EL1 DR1 CR1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CL0 HR1 DR0 CL1 EL1 DR1 DR1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CL0 HR1 DR1 CL1 CL1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR0 CL0 CL0 AR1 BR1 DL0 CL1 ER1 AR0 HR1,RWL 4 2)::
(makeTM BR0 CL0 CR0 HR1 DR0 CL1 EL1 DR1 BL1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CR0 HR1 DR0 CL1 EL1 DR1 CL1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CR0 HR1 DR0 CL1 EL1 DR1 CR1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CR0 HR1 DR0 CL1 EL1 DR1 DR1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CR0 HR1 DL1 DL0 ER1 AR1 AL1 DR1,RWL 6 2)::
(makeTM BR0 CL0 CR0 HR1 DR1 CL1 CL1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR0 CL0 CR0 BR1 DL1 AL0 EL0 HR1 AR0 CL1,RWL 6 2)::
(makeTM BR0 CL0 CR0 BR1 DL1 EL0 AL1 HR1 BR0 EL1,RWL 2 2)::
(makeTM BR0 CL0 CR0 BR1 DR1 AL1 ER0 HR1 EL1 CL0,RWL 8 2)::
(makeTM BR0 CL0 CR0 ER1 DL0 BR1 AL1 AR1 DR1 HR1,RWL 3 4)::
(makeTM BR0 CL0 CL1 HR1 DL1 EL0 ER1 DR1 AL1 DR0,RWL 1 3)::
(makeTM BR0 CL0 CL1 HR1 DL1 ER0 CR1 AL0 DR1 AR1,RWL 3 2)::
(makeTM BR0 CL0 CL1 AR0 DR1 EL0 BR1 DR1 HR1 BL1,RWL 1 4)::
(makeTM BR0 CL0 CL1 AR1 DL1 ER0 AL1 DL0 CR1 HR1,RWL 2 2)::
(makeTM BR0 CL0 CL1 BL1 DR0 AL1 HR1 ER0 BR1 ER1,RWL 2 2)::
(makeTM BR0 CL0 CL1 BL1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CL1 BL1 DR1 AL1 HR1 ER0 BR1 ER1,RWL 2 2)::
(makeTM BR0 CL0 CL1 BL1 DR1 AL1 HR1 EL1 BR1 ER1,RWL 2 2)::
(makeTM BR0 CL0 CL1 BL1 DR1 AL1 HR1 ER1 BR1 ER1,RWL 2 2)::
(makeTM BR0 CL0 CL1 BL1 DR1 CL1 HR1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR0 CL0 CL1 BR1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 CL0 CL1 CL0 BR1 DR1 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL0 CL1 CR0 DL1 AL1 EL0 HR1 ER1 BR1,RWL 8 2)::
(makeTM BR0 CL0 CL1 DR1 AL1 ER1 CR1 AR1 AR0 HR1,RWL 3 3)::
(makeTM BR0 CL0 CL1 DR1 DL0 HR1 AR1 ER0 AL0 EL1,RWL 3 2)::
(makeTM BR0 CL0 CL1 ER0 DR1 BR1 HR1 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL0 CL1 ER0 DR1 BR1 HR1 CL1 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL0 CL1 ER1 AR1 DL0 AL1 BL0 CR0 HR1,RWL 16 2)::
(makeTM BR0 CL0 CL1 ER1 DR0 CL1 AL1 DR1 HR1 BR1,RWL 2 3)::
(makeTM BR0 CL0 CL1 ER1 DL1 HR1 AL1 BR0 AL0 ER0,RWL 3 3)::
(makeTM BR0 CL0 CR1 HR1 DL1 EL0 ER1 DR1 AL1 DR0,RWL 1 3)::
(makeTM BR0 CL0 CR1 HR1 DR1 CL1 EL1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR0 CL0 CR1 HR1 DR1 CL1 EL1 ER0 BR1 AL0,RWL 3 3)::
(makeTM BR0 CL0 CR1 HR1 DR1 CL1 ER1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR0 CL0 CR1 AL0 DL0 DR0 AR1 EL1 CL1 HR1,RWL 7 2)::
(makeTM BR0 CL0 CR1 AL0 DR0 ER0 BL1 HR1 DL1 AR1,RWL 17 2)::
(makeTM BR0 CL0 CR1 AR1 DL1 DR0 AL1 EL0 CL1 HR1,RWL 9 2)::
(makeTM BR0 CL0 CR1 AR1 DR1 EL1 AL1 CR0 DL0 HR1,RWL 4 3)::
(makeTM BR0 CL0 CR1 BL1 BL0 DR1 ER1 AR0 BR1 HR1,RWL 25 2)::
(makeTM BR0 CL0 CR1 BL1 DL1 ER0 HR1 AL1 BL0 ER1,RWL 2 3)::
(makeTM BR0 CL0 CR1 BR1 AL1 DR0 CL1 ER0 HR1 BL1,RWL 4 2)::
(makeTM BR0 CL0 CR1 BR1 AL1 DR0 CL1 ER1 HR1 DR0,RWL 4 2)::
(makeTM BR0 CL0 CR1 BR1 DL1 AR0 HR1 EL0 AR1 BL0,RWL 6 3)::
(makeTM BR0 CL0 CR1 BR1 DL1 EL0 HR1 AL1 BR0 EL1,RWL 2 2)::
(makeTM BR0 CL0 CR1 CL1 DR1 AL0 ER1 AR1 AL1 HR1,RWL 4 3)::
(makeTM BR0 CL0 CR1 DL0 AL1 DR0 EL1 AR0 BL1 HR1,RWL 4 3)::
(makeTM BR0 CL0 CR1 DR0 AL1 EL0 BR1 HR1 BL0 AL1,RWL 4 2)::
(makeTM BR0 CL0 CR1 DR0 AL1 EL1 BR1 HR1 AL0 EL0,RWL 4 2)::
(makeTM BR0 CL0 CR1 DR1 AL1 BL0 ER0 HR1 AR1 EL0,RWL 7 2)::
(makeTM BR0 CL0 CR1 DR1 AL1 BL0 ER1 HR1 AR0 AR1,RWL 8 2)::
(makeTM BR0 CL0 CR1 DR1 AL1 CL0 ER1 HR1 AR1 ER0,RWL 4 4)::
(makeTM BR0 CL0 CR1 DR1 AL1 DL1 BR1 ER0 HR1 DL0,RWL 1 4)::
(makeTM BR0 CL0 CR1 DR1 BL1 BR1 HR1 ER0 EL1 AR0,RWL 5 2)::
(makeTM BR0 CL0 CR1 DR1 BL1 ER1 AR0 DL1 AR1 HR1,RWL 1 3)::
(makeTM BR0 CL0 CR1 DR1 DL1 ER1 BR1 AL1 AR0 HR1,RWL 2 2)::
(makeTM BR0 CL0 CR1 EL0 DL1 BR0 HR1 BL1 BR1 AL1,RWL 17 2)::
(makeTM BR0 CL0 CR1 EL0 DR1 CR1 BL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 CL0 CR1 ER0 DL1 CR1 ER1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 CL0 CR1 ER1 DL1 BL0 AL1 DL0 AR1 HR1,RWL 6 2)::
(makeTM BR0 CR0 AL1 BR1 DL1 CL1 AL0 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR0 CR0 CL0 HR1 DL1 CR1 CR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR0 CR0 CL0 BR1 DR1 EL0 CL1 HR1 AR1 AL0,RWL 2 2)::
(makeTM BR0 CR0 CL0 EL0 DR1 BR0 BL1 HR1 AR1 EL1,RWL 2 3)::
(makeTM BR0 CR0 CL0 ER1 DL1 BL0 BR1 CL0 AR1 HR1,RWL 3 2)::
(makeTM BR0 CR0 CR0 HR1 DL1 CR1 CR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR0 CR0 CR0 HR1 DR1 AR1 EL1 DL0 CR1 CL1,RWL 3 3)::
(makeTM BR0 CR0 CR0 ER1 DL1 CR1 AL1 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 CR0 CL1 HR1 DL0 AR1 ER1 CL0 ER1 CR1,RWL 7 2)::
(makeTM BR0 CR0 CL1 HR1 DL0 CR1 ER1 DL1 AL1 AR1,RWL 2 2)::
(makeTM BR0 CR0 CL1 HR1 DL0 CR1 ER1 DL1 AR1 AL0,RWL 2 2)::
(makeTM BR0 CR0 CL1 HR1 DL0 CR1 ER1 DL1 AR1 AR1,RWL 2 2)::
(makeTM BR0 CR0 CL1 HR1 DL0 CR1 ER1 DL1 CL1 AR1,RWL 2 2)::
(makeTM BR0 CR0 CL1 HR1 DL0 CR1 ER1 DL1 CR1 AR1,RWL 2 2)::
(makeTM BR0 CR0 CL1 HR1 DL0 CR1 ER1 DL1 DL1 AR1,RWL 2 2)::
(makeTM BR0 CR0 CL1 HR1 DL0 CR1 ER1 DL1 DR1 AR1,RWL 2 2)::
(makeTM BR0 CR0 CL1 HR1 DL1 CR1 EL1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR0 CR0 CL1 HR1 DL1 CR1 ER1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR0 CR0 CL1 HR1 DR1 ER0 AR1 EL1 DL1 EL0,RWL 6 2)::
(makeTM BR0 CR0 CL1 HR1 DR1 EL1 ER0 CL0 AR1 CL1,RWL 4 3)::
(makeTM BR0 CR0 CL1 AR0 DL0 BR1 EL0 HR1 ER1 CL0,RWL 24 2)::
(makeTM BR0 CR0 CL1 AL1 DL0 ER0 DR1 BR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 CR0 CL1 AR1 DL1 BL0 CR1 EL0 AL0 HR1,RWL 6 2)::
(makeTM BR0 CR0 CL1 AR1 DL1 ER1 BR1 ER0 HR1 BL0,RWL 2 3)::
(makeTM BR0 CR0 CL1 AR1 DR1 EL0 HR1 BR1 BL0 AL1,RWL 3 2)::
(makeTM BR0 CR0 CL1 BL1 DL0 ER0 DR1 AR1 HR1 AL0,RWL 3 2)::
(makeTM BR0 CR0 CL1 BR1 BR0 DL1 AL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 CR0 CL1 BR1 DL0 DL1 AL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR0 CR0 CL1 BR1 DL0 ER1 AR1 AL0 HR1 AR1,RWL 9 2)::
(makeTM BR0 CR0 CL1 BR1 DR0 EL1 HR1 AL1 AL1 DL0,RWL 2 2)::
(makeTM BR0 CR0 CL1 BR1 DL1 DL1 AL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 CR0 CL1 BR1 DL1 ER0 BR0 DL0 HR1 AR1,RWL 6 2)::
(makeTM BR0 CR0 CL1 BR1 DR1 DL1 AL1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 CR0 CL1 CR0 DR1 EL1 HR1 BR1 CL0 AL0,RWL 2 3)::
(makeTM BR0 CR0 CL1 DL0 DL0 BR0 AR1 EL1 HR1 DL1,RWL 2 3)::
(makeTM BR0 CR0 CL1 DL1 BR1 BL1 HR1 EL0 ER1 AL0,RWL 5 2)::
(makeTM BR0 CR0 CL1 DL1 DL0 ER0 AR1 AL0 HR1 AL0,RWL 2 2)::
(makeTM BR0 CR0 CL1 DL1 DL0 ER0 AR1 AL0 HR1 CL1,RWL 2 2)::
(makeTM BR0 CR0 CL1 DL1 DL0 ER0 AR1 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR0 CR0 CL1 DL1 DL0 ER1 AR1 AL0 HR1 BL0,RWL 3 2)::
(makeTM BR0 CR0 CL1 ER1 DL0 CR1 BR1 DL1 HR1 AR1,RWL 3 2)::
(makeTM BR0 CR0 CR1 HR1 DL1 AL0 EL0 BL1 ER1 AL1,RWL 2 3)::
(makeTM BR0 CR0 CR1 HR1 DL1 AL0 EL0 CL1 ER1 AL1,RWL 5 2)::
(makeTM BR0 CR0 CR1 HR1 DL1 AL0 EL0 DL1 ER1 AL1,RWL 2 3)::
(makeTM BR0 CR0 CR1 HR1 DR1 ER0 EL1 DL1 AR1 DL0,RWL 1 3)::
(makeTM BR0 CR0 CR1 AR1 DL1 AR1 EL0 BL1 HR1 DL0,RWL 7 3)::
(makeTM BR0 CR0 CR1 AR1 DL1 BR0 BL1 EL0 CL0 HR1,RWL 4 2)::
(makeTM BR0 CR0 CR1 BL1 DL1 AR0 EL0 BR1 DL0 HR1,RWL 6 2)::
(makeTM BR0 CR0 CR1 BL1 DL1 CR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR0 CR0 CR1 CL0 DL1 AR0 BL1 EL1 DL0 HR1,RWL 10 2)::
(makeTM BR0 CR0 CR1 DL0 DR1 ER1 BL1 CL0 AR1 HR1,RWL 4 2)::
(makeTM BR0 CR0 CR1 EL0 DL1 CR1 AL0 BL1 HR1 AL0,RWL 2 3)::
(makeTM BR0 CR0 CR1 ER1 DL1 AL0 BL0 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL0 DL0 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL0 DL0 ER0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL0 DL0 ER0 DL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL0 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL0 DL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR0 CL1 AL1 BR1 AL0 DL1 DR1 ER1 HR1 BR0,RWL 2 3)::
(makeTM BR0 CL1 AL1 BR1 AL1 DL0 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL1 DL0 ER0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL1 DL0 ER0 DL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL1 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL1 DL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR0 CL1 AL1 BR1 AL1 DL1 BL0 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 AL1 DR1 EL1 CR0 HR1 DL1,RWL 6 2)::
(makeTM BR0 CL1 AL1 BR1 BL1 DL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR0 CL1 AL1 BR1 BR1 DL0 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 BR1 DL0 ER0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 BR1 DL0 ER0 DL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 BR1 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 BR1 DL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR0 CL1 AL1 BR1 CR1 DL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR0 CL1 AL1 BR1 DL0 EL0 BR0 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DL0 EL0 BR0 DL1 HR1 DL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DL0 EL1 BR0 DL1 HR1 AR0,RWL 3 2)::
(makeTM BR0 CL1 AL1 BR1 DL0 EL1 BR0 DL1 HR1 DL0,RWL 3 2)::
(makeTM BR0 CL1 AL1 BR1 DL1 DL0 ER0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DL1 DL0 ER0 DL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DL1 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DL1 EL0 BR0 AR0 HR1 DL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DL1 EL0 BR0 DL1 HR1 DL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DL1 EL1 BR0 DL1 HR1 DL0,RWL 3 2)::
(makeTM BR0 CL1 AL1 BR1 DR1 DL0 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DR1 DL0 ER0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DR1 DL0 ER0 DL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DR1 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DR1 EL0 HR1 BR1 DR0 EL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DR1 EL0 BR0 DL1 HR1 DL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 BR1 DR1 EL1 BR0 DL1 HR1 DL0,RWL 3 2)::
(makeTM BR0 CL1 AL1 CL0 DR1 BR0 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL1 AL1 CL0 DR1 ER0 BR1 HR1 AL0 BL1,RWL 2 2)::
(makeTM BR0 CL1 AL1 CL0 DR1 ER0 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL1 CL0 HR1 BR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL1 CL0 HR1 BR1 DR1 ER0 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL1 CL0 HR1 BR1 DR1 ER0 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL1 CL0 HR1 DL1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR0 CL1 CL0 HR1 DR1 EL0 AL1 DR1 DR0 EL1,RWL 2 2)::
(makeTM BR0 CL1 CL0 AL0 DL1 HR1 ER1 BR0 AL1 DR0,RWL 9 2)::
(makeTM BR0 CL1 CL0 AR1 AL1 DL0 DR1 EL1 HR1 BL0,RWL 7 2)::
(makeTM BR0 CL1 CL0 AR1 AL1 DL0 EL1 HR1 AL0 ER0,RWL 7 2)::
(makeTM BR0 CL1 CL0 AR1 AL1 DL1 ER1 EL0 HR1 BL0,RWL 6 2)::
(makeTM BR0 CL1 CL0 BR1 DR1 CL1 AL1 ER1 HR1 BR0,RWL 2 2)::
(makeTM BR0 CL1 CL0 CL1 DR1 ER0 BR1 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL1 CL0 CR1 DR1 ER0 BL1 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL1 CL0 ER0 DR1 AL1 ER0 HR1 EL1 AL0,RWL 2 3)::
(makeTM BR0 CL1 CL0 ER0 DR1 BR1 CL1 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 CL1 CR0 HR1 DL1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR0 CL1 CR0 HR1 DR1 EL0 AL1 DR1 DR0 EL1,RWL 2 2)::
(makeTM BR0 CL1 CR0 BL1 DL1 CR1 AR1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 CL1 CR0 BR1 DL0 AL0 EL1 HR1 AL1 EL0,RWL 6 2)::
(makeTM BR0 CL1 CL1 AR1 AL1 DL0 ER1 BL0 DR1 HR1,RWL 1 4)::
(makeTM BR0 CL1 CL1 BR1 AL1 DL1 HR1 ER0 AR1 DR1,RWL 6 2)::
(makeTM BR0 CL1 CL1 DR0 DL0 HR1 EL0 DL1 AR1 AL0,RWL 20 2)::
(makeTM BR0 CL1 CL1 ER0 DL1 DR0 BR1 AL0 HR1 AR1,RWL 5 2)::
(makeTM BR0 CL1 CL1 ER1 DL0 CR0 AR1 BL0 DR0 HR1,RWL 6 2)::
(makeTM BR0 CL1 CR1 HR1 AL0 DR1 EL1 ER0 AR0 EL1,RWL 13 2)::
(makeTM BR0 CL1 CR1 HR1 DR1 CL0 ER1 AR0 AL0 ER0,RWL 4 2)::
(makeTM BR0 CL1 CR1 AR0 DR0 AR1 DL1 EL0 BL1 HR1,RWL 5 2)::
(makeTM BR0 CL1 CR1 AR0 DL1 ER0 AL0 AL1 HR1 BR1,RWL 4 2)::
(makeTM BR0 CL1 CR1 AR1 AL1 DR1 ER1 DL0 CR0 HR1,RWL 21 2)::
(makeTM BR0 CL1 CR1 AR1 DL1 CR1 HR1 EL0 AL1 BL0,RWL 4 2)::
(makeTM BR0 CL1 CR1 BR1 AL1 DR0 BR1 ER1 HR1 AL0,RWL 6 2)::
(makeTM BR0 CL1 CR1 BR1 DL1 ER0 HR1 EL1 AL1 AL0,RWL 8 2)::
(makeTM BR0 CL1 CR1 BR1 DL1 ER0 AL0 AR1 HR1 DR1,RWL 6 2)::
(makeTM BR0 CL1 CR1 DL0 AL1 BL1 DR1 EL0 HR1 BR0,RWL 5 2)::
(makeTM BR0 CL1 CR1 DL0 AL1 EL0 AR1 AR1 HR1 BL0,RWL 4 3)::
(makeTM BR0 CL1 CR1 DL0 AL1 EL0 AR1 CR0 HR1 BL0,RWL 4 3)::
(makeTM BR0 CL1 CR1 DR0 AL0 BR1 DL1 ER1 HR1 AR0,RWL 7 2)::
(makeTM BR0 CL1 CR1 DR0 AL1 BR0 DL1 EL0 BL1 HR1,RWL 3 2)::
(makeTM BR0 CL1 CR1 DL1 AL1 EL0 DR1 BR0 HR1 BL0,RWL 4 2)::
(makeTM BR0 CL1 CR1 DR1 AL0 BR1 EL1 ER0 HR1 AR0,RWL 6 2)::
(makeTM BR0 CL1 CR1 EL1 DL1 CR0 BL0 AL0 BL1 HR1,RWL 5 2)::
(makeTM BR0 CR1 AL1 CR0 DR1 HR1 EL1 BL0 AR1 DL0,RWL 9 2)::
(makeTM BR0 CR1 AL1 CL1 DL0 EL0 EL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR0 CR1 CL0 HR1 DL1 AR0 ER0 DL0 CL1 ER1,RWL 4 3)::
(makeTM BR0 CR1 CL0 HR1 DL1 DR1 AR0 EL0 CL1 CR0,RWL 5 2)::
(makeTM BR0 CR1 CL0 BR1 DR1 CL1 AL1 ER1 HR1 BR0,RWL 2 2)::
(makeTM BR0 CR1 CL0 CL1 DL1 EL0 BR1 HR1 ER1 AR0,RWL 2 2)::
(makeTM BR0 CR1 CL0 DL0 DL1 ER0 AR1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 CR1 CL0 DR1 BR1 DR0 EL1 AL0 CL1 HR1,RWL 2 2)::
(makeTM BR0 CR1 CL0 ER0 DL1 HR1 ER1 DL0 AR1 AR1,RWL 3 3)::
(makeTM BR0 CR1 CR0 BL1 DL1 CR1 AR1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 CR1 CL1 HR1 DL0 CL0 EL0 AL1 ER1 AR0,RWL 3 2)::
(makeTM BR0 CR1 CL1 HR1 DL0 DR0 ER1 BL1 AR0 ER0,RWL 7 2)::
(makeTM BR0 CR1 CL1 HR1 DR1 ER0 BR0 AL1 EL1 DL0,RWL 2 2)::
(makeTM BR0 CR1 CL1 AL0 DL0 HR1 DR1 ER0 AL1 BR1,RWL 2 2)::
(makeTM BR0 CR1 CL1 AL0 DR1 EL0 ER1 BR1 HR1 BL1,RWL 2 3)::
(makeTM BR0 CR1 CL1 AR0 DL1 DR0 BR1 EL0 BL1 HR1,RWL 24 2)::
(makeTM BR0 CR1 CL1 AR1 DL1 BR1 AL1 EL0 HR1 CL1,RWL 3 3)::
(makeTM BR0 CR1 CL1 AR1 DL1 BR1 AR1 EL0 HR1 CL1,RWL 3 3)::
(makeTM BR0 CR1 CL1 BL1 DL1 EL0 ER1 BR0 HR1 AR0,RWL 3 2)::
(makeTM BR0 CR1 CL1 BL1 DL1 EL0 ER1 CL1 HR1 AR0,RWL 3 2)::
(makeTM BR0 CR1 CL1 BR1 DL1 EL0 AR1 DL0 HR1 DR0,RWL 2 3)::
(makeTM BR0 CR1 CL1 CR0 DL1 AR1 AR1 EL0 HR1 CL1,RWL 2 3)::
(makeTM BR0 CR1 CL1 CR0 DL1 AR1 ER1 EL0 HR1 CL1,RWL 2 3)::
(makeTM BR0 CR1 CL1 DL1 DL0 BL0 EL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR0 CR1 CL1 DR1 DL1 AR0 ER0 BL0 HR1 AR1,RWL 18 2)::
(makeTM BR0 CR1 CL1 EL0 DL1 BL0 CR1 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR0 CR1 CL1 ER0 DR0 HR1 EL0 DL1 AR1 DL0,RWL 10 2)::
(makeTM BR0 CR1 CL1 ER0 DL1 CR0 AR1 DL0 HR1 DL1,RWL 7 3)::
(makeTM BR0 CR1 CL1 ER1 DL1 CR0 AR1 DL0 HR1 CL0,RWL 7 3)::
(makeTM BR0 CR1 CL1 ER1 DL1 CR0 AR1 DL0 HR1 CR1,RWL 7 3)::
(makeTM BR0 CR1 CR1 HR1 DL0 AR0 EL1 DL1 AL0 ER1,RWL 2 2)::
(makeTM BR0 CR1 CR1 HR1 DL1 AL0 ER1 CL0 AR1 DR1,RWL 2 2)::
(makeTM BR0 CR1 CR1 HR1 DL1 AR0 ER0 DL0 CL1 ER1,RWL 4 3)::
(makeTM BR0 CR1 CR1 DL0 DL1 ER0 HR1 AL0 EL1 BL1,RWL 3 3)::
(makeTM BR0 CR1 CR1 ER1 DL0 CR1 AL1 DL1 HR1 BR0,RWL 2 2)::
(makeTM BR0 CR1 CR1 ER1 DL1 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 DL0 AL1 CR0 BR1 AL0 EL0 HR1 CL1 ER1,RWL 4 2)::
(makeTM BR0 DL0 AL1 CR0 BR1 CR1 DR1 EL0 HR1 CL1,RWL 2 3)::
(makeTM BR0 DL0 AL1 CR0 BR1 ER0 EL1 HR1 CL1 EL0,RWL 2 3)::
(makeTM BR0 DL0 AL1 CR1 BL1 CR0 EL0 HR1 ER0 BL0,RWL 15 2)::
(makeTM BR0 DL0 CL0 AR1 DL1 EL1 BR1 DR1 HR1 AL0,RWL 5 3)::
(makeTM BR0 DL0 CL0 BR0 DL1 HR1 ER1 AL1 AR0 CR1,RWL 2 3)::
(makeTM BR0 DL0 CL0 BR1 DR1 CL1 ER0 AR1 BL1 HR1,RWL 2 2)::
(makeTM BR0 DL0 CL0 BR1 DR1 CL1 EL1 BR0 HR1 AL1,RWL 2 3)::
(makeTM BR0 DL0 CL0 CR1 AL1 CR0 EL1 HR1 CR1 BL0,RWL 3 3)::
(makeTM BR0 DL0 CL0 CR1 DR1 BR0 AL1 ER1 CR0 HR1,RWL 14 2)::
(makeTM BR0 DL0 CL0 DR1 AL1 DR0 ER1 BL0 CR1 HR1,RWL 4 2)::
(makeTM BR0 DL0 CL0 EL0 DR1 AR0 BL1 CR0 CL1 HR1,RWL 3 3)::
(makeTM BR0 DL0 CL0 ER0 DL1 HR1 EL1 AL1 AR1 BL1,RWL 3 3)::
(makeTM BR0 DL0 CR0 HR1 DL1 CR1 EL1 EL0 AL0 BR0,RWL 24 2)::
(makeTM BR0 DL0 CR0 HR1 DL1 DR1 ER1 EL0 AR1 EL1,RWL 6 3)::
(makeTM BR0 DL0 CR0 AL0 DR1 ER0 AL1 BR1 CL1 HR1,RWL 5 2)::
(makeTM BR0 DL0 CR0 AL0 DR1 EL1 AL1 BR1 DL1 HR1,RWL 5 2)::
(makeTM BR0 DL0 CR0 BR0 DL1 CR1 EL1 BL0 AL0 HR1,RWL 24 2)::
(makeTM BR0 DL0 CR0 BL1 DR0 CR1 EL1 BL0 AL1 HR1,RWL 2 2)::
(makeTM BR0 DL0 CR0 BL1 DR1 CR1 EL1 BL0 HR1 AL1,RWL 2 2)::
(makeTM BR0 DL0 CR0 BR1 DL1 HR1 AL1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 DL0 CR0 CR1 AL1 BR1 EL0 HR1 AR0 CL0,RWL 2 4)::
(makeTM BR0 DL0 CR0 EL0 DR0 DR1 BL1 CR1 AL0 HR1,RWL 2 4)::
(makeTM BR0 DL0 CR0 ER0 DL1 HR1 AL1 CL1 AR1 BR1,RWL 5 2)::
(makeTM BR0 DL0 CR0 ER1 BL1 DR1 AL1 BR1 AR1 HR1,RWL 5 2)::
(makeTM BR0 DL0 CR0 ER1 DR1 BL0 AL1 BR1 AR1 HR1,RWL 5 2)::
(makeTM BR0 DL0 CR0 ER1 DR1 DR1 AL1 BR1 AR1 HR1,RWL 5 2)::
(makeTM BR0 DL0 CL1 HR1 DL1 AL1 ER0 DL1 CL1 ER1,RWL 2 2)::
(makeTM BR0 DL0 CL1 HR1 DL1 ER0 CR1 DL1 AL1 ER1,RWL 2 3)::
(makeTM BR0 DL0 CL1 HR1 DR1 AL0 AR1 ER0 BL1 CR1,RWL 5 3)::
(makeTM BR0 DL0 CL1 HR1 DR1 AL1 ER0 DL1 CL1 ER1,RWL 2 2)::
(makeTM BR0 DL0 CL1 HR1 DR1 ER0 CR1 DL1 AL1 ER1,RWL 2 3)::
(makeTM BR0 DL0 CL1 AL0 DR1 BL1 HR1 ER0 BR1 AL1,RWL 4 2)::
(makeTM BR0 DL0 CL1 AR0 DL1 BR1 EL0 HR1 BR1 EL1,RWL 4 3)::
(makeTM BR0 DL0 CL1 AR0 DL1 ER0 EL0 HR1 BR1 EL1,RWL 4 3)::
(makeTM BR0 DL0 CL1 AL1 BR1 HR1 DR1 ER0 AL0 BR1,RWL 2 2)::
(makeTM BR0 DL0 CL1 AL1 BR1 BL1 DR1 EL0 HR1 CR0,RWL 5 2)::
(makeTM BR0 DL0 CL1 AR1 AL1 AL0 HR1 EL1 BR1 ER1,RWL 2 2)::
(makeTM BR0 DL0 CL1 AR1 AL1 BL1 HR1 EL1 BR1 BL0,RWL 6 3)::
(makeTM BR0 DL0 CL1 BL0 DR1 AR1 AL1 ER1 CR0 HR1,RWL 5 2)::
(makeTM BR0 DL0 CL1 BL1 DR1 AL1 HR1 ER0 BR1 BR0,RWL 3 2)::
(makeTM BR0 DL0 CL1 BR1 DL0 EL1 DR1 BR0 HR1 AL0,RWL 2 3)::
(makeTM BR0 DL0 CL1 BR1 DL1 CR0 EL1 CL1 AL1 HR1,RWL 3 2)::
(makeTM BR0 DL0 CL1 BR1 DL1 EL1 BR0 DL1 HR1 AL1,RWL 3 2)::
(makeTM BR0 DL0 CL1 BR1 DR1 CR1 AL1 EL0 HR1 CR0,RWL 5 2)::
(makeTM BR0 DL0 CL1 BR1 DR1 EL1 BR0 DL1 HR1 AL1,RWL 3 2)::
(makeTM BR0 DL0 CL1 CR0 AL1 CR1 BR1 EL1 HR1 DL1,RWL 2 3)::
(makeTM BR0 DL0 CL1 CR0 AR1 HR1 AL1 EL1 BR1 AL0,RWL 4 2)::
(makeTM BR0 DL0 CL1 CR0 AR1 HR1 BL0 EL1 BR1 AL0,RWL 4 3)::
(makeTM BR0 DL0 CL1 CR0 AR1 BL0 EL1 AL1 BL1 HR1,RWL 4 2)::
(makeTM BR0 DL0 CL1 CR0 AR1 CR1 HR1 EL1 BR1 EL0,RWL 4 3)::
(makeTM BR0 DL0 CL1 CR0 AR1 EL1 HR1 BR1 CL0 AL0,RWL 3 2)::
(makeTM BR0 DL0 CL1 CR0 DL1 AL0 ER1 BL1 HR1 BR0,RWL 4 2)::
(makeTM BR0 DL0 CL1 CR1 AR1 CL0 BL0 ER1 DR0 HR1,RWL 12 2)::
(makeTM BR0 DL0 CL1 ER0 AR1 BL1 ER1 DL1 HR1 CR0,RWL 7 2)::
(makeTM BR0 DL0 CL1 ER0 AR1 BR1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL0 CL1 EL1 DR1 AR0 BL1 CR0 AL0 HR1,RWL 12 2)::
(makeTM BR0 DL0 CL1 ER1 AR0 AR1 EL1 HR1 CR1 EL0,RWL 12 2)::
(makeTM BR0 DL0 CL1 ER1 DL0 HR1 DR1 ER0 AL0 BR1,RWL 2 3)::
(makeTM BR0 DL0 CL1 ER1 DR0 AL1 BR1 CR1 HR1 BR1,RWL 2 2)::
(makeTM BR0 DL0 CL1 ER1 DR1 AL0 AL1 BL0 CR0 HR1,RWL 2 2)::
(makeTM BR0 DL0 CL1 ER1 DR1 AL0 BR1 DR1 HR1 DR0,RWL 6 2)::
(makeTM BR0 DL0 CR1 HR1 AL1 AR1 EL1 AL0 ER1 DR0,RWL 3 3)::
(makeTM BR0 DL0 CR1 HR1 AL1 CR1 ER1 DL1 CL1 CR0,RWL 2 3)::
(makeTM BR0 DL0 CR1 HR1 AL1 CR1 ER1 DL1 CR1 CR0,RWL 2 3)::
(makeTM BR0 DL0 CR1 HR1 DR0 AR1 EL1 CR0 AL0 AR0,RWL 15 2)::
(makeTM BR0 DL0 CR1 HR1 DL1 AL1 ER0 DL1 CL1 ER1,RWL 2 2)::
(makeTM BR0 DL0 CR1 HR1 DL1 CR0 EL1 EL1 AL0 BL1,RWL 3 3)::
(makeTM BR0 DL0 CR1 HR1 DL1 ER0 CR1 DL1 AL1 ER1,RWL 2 3)::
(makeTM BR0 DL0 CR1 HR1 DR1 AL1 ER0 DL1 CL1 ER1,RWL 2 2)::
(makeTM BR0 DL0 CR1 HR1 DR1 DR0 AL0 ER1 AL1 AR0,RWL 7 2)::
(makeTM BR0 DL0 CR1 HR1 DR1 ER1 EL1 AR1 AL0 CR0,RWL 3 3)::
(makeTM BR0 DL0 CR1 AL0 AL1 CR0 EL1 HR1 BL1 AR0,RWL 4 2)::
(makeTM BR0 DL0 CR1 AL0 AL1 ER0 BR1 AL0 DR1 HR1,RWL 4 2)::
(makeTM BR0 DL0 CR1 AR0 AL1 AR1 EL0 HR1 ER1 CL0,RWL 3 2)::
(makeTM BR0 DL0 CR1 AR0 AL1 DR0 BR1 EL0 CL0 HR1,RWL 2 2)::
(makeTM BR0 DL0 CR1 AR1 AL1 AR0 EL0 HR1 CL0 DL1,RWL 12 2)::
(makeTM BR0 DL0 CR1 AR1 AL1 AR0 EL0 HR1 CL0 EL1,RWL 7 3)::
(makeTM BR0 DL0 CR1 AR1 DR1 HR1 AL0 ER1 AL1 BL0,RWL 4 3)::
(makeTM BR0 DL0 CR1 AR1 DR1 HR1 AL0 ER1 AL1 BR0,RWL 4 3)::
(makeTM BR0 DL0 CR1 AR1 DR1 ER1 AL1 DL0 DR0 HR1,RWL 4 3)::
(makeTM BR0 DL0 CR1 BL0 AL1 ER0 DR1 CR0 HR1 AL1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BL0 AL1 ER0 DR1 CR0 HR1 BL0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BL0 AL1 ER1 DR1 CR0 HR1 AL1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BL0 AL1 ER1 DR1 CR0 HR1 DL0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BL0 DL1 ER0 BL1 AR0 DR1 HR1,RWL 3 3)::
(makeTM BR0 DL0 CR1 BL1 AL1 AR0 EL1 HR1 AL1 CL0,RWL 8 2)::
(makeTM BR0 DL0 CR1 BL1 AL1 DR0 ER1 BL0 AR1 HR1,RWL 13 2)::
(makeTM BR0 DL0 CR1 BL1 DL1 AR1 HR1 EL0 AL1 BL1,RWL 6 3)::
(makeTM BR0 DL0 CR1 BR1 AL1 BR0 DR1 EL0 HR1 BL1,RWL 2 3)::
(makeTM BR0 DL0 CR1 BR1 AL1 ER0 CL0 DL1 AR1 HR1,RWL 7 2)::
(makeTM BR0 DL0 CR1 BR1 AL1 ER1 DR1 CR1 HR1 BR0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 CL1 AL1 HR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DR0 CL1 EL0 AL1 AL1 HR1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DR0 CL1 EL1 AL1 AR1 HR1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER0 AL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER0 AL1 HR1 BR0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER0 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER1 AL1 HR1 BR0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER1 AL1 HR1 CR0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER1 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER1 AL1 HR1 DL1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 EL1 HR1 AL1 BL0 EL1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 EL1 HR1 AL1 BR0 EL1,RWL 2 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 EL1 HR1 AL1 DR0 EL1,RWL 2 2)::
(makeTM BR0 DL0 CR1 CL0 AL1 ER0 BR0 BL0 BR1 HR1,RWL 7 2)::
(makeTM BR0 DL0 CR1 CR0 AL1 CR1 BR1 EL1 HR1 DL1,RWL 2 3)::
(makeTM BR0 DL0 CR1 CR0 DR1 EL0 AL1 BR1 HR1 DL1,RWL 3 2)::
(makeTM BR0 DL0 CR1 CL1 BL1 AL1 DR1 EL0 HR1 BR0,RWL 5 2)::
(makeTM BR0 DL0 CR1 DR0 AL1 AR0 CL1 ER1 BR0 HR1,RWL 3 3)::
(makeTM BR0 DL0 CR1 DR1 AL1 AR0 CL1 ER0 AR1 HR1,RWL 8 2)::
(makeTM BR0 DL0 CR1 DR1 AL1 BR1 ER0 CL0 AL0 HR1,RWL 3 3)::
(makeTM BR0 DL0 CR1 EL0 AL1 AR0 EL1 HR1 BL1 EL0,RWL 3 3)::
(makeTM BR0 DL0 CR1 ER0 AL1 AR0 CL1 HR1 AR1 AR1,RWL 3 3)::
(makeTM BR0 DL0 CR1 ER0 AL1 AR0 CL1 HR1 BL1 AR1,RWL 3 3)::
(makeTM BR0 DL0 CR1 ER0 AL1 AR0 CL1 HR1 CL1 AR1,RWL 3 3)::
(makeTM BR0 DL0 CR1 ER0 AL1 AR0 CL1 HR1 EL0 AR1,RWL 3 3)::
(makeTM BR0 DL0 CR1 ER0 AL1 BR0 EL1 HR1 BL1 EL0,RWL 2 3)::
(makeTM BR0 DL0 CR1 ER0 AL1 BR1 AL1 BL0 AL0 HR1,RWL 35 2)::
(makeTM BR0 DL0 CR1 ER0 AL1 CR1 BR1 DL1 HR1 AL0,RWL 2 3)::
(makeTM BR0 DL0 CR1 ER0 AL1 CR1 BR1 DL1 HR1 CR1,RWL 2 3)::
(makeTM BR0 DL0 CR1 ER0 DL1 AR1 AR0 CL0 BL1 HR1,RWL 5 2)::
(makeTM BR0 DL0 CR1 ER1 AL0 HR1 EL1 ER0 AL1 AR1,RWL 5 2)::
(makeTM BR0 DL0 CR1 ER1 AL0 CR0 AL1 CL1 AR1 HR1,RWL 4 2)::
(makeTM BR0 DL0 CR1 ER1 AL1 HR1 EL1 CR0 AL1 AR1,RWL 5 2)::
(makeTM BR0 DL0 CR1 ER1 AL1 HR1 EL1 ER0 AL1 AR1,RWL 5 2)::
(makeTM BR0 DL0 CR1 ER1 AL1 BL1 EL0 HR1 CL1 AR0,RWL 6 2)::
(makeTM BR0 DL0 CR1 ER1 AL1 CL1 EL1 HR1 AL0 ER0,RWL 10 2)::
(makeTM BR0 DL0 CR1 ER1 AL1 CR1 CR0 DL1 HR1 BR1,RWL 2 3)::
(makeTM BR0 DL0 CR1 ER1 AL1 EL0 CL1 HR1 BR1 BR0,RWL 1 4)::
(makeTM BR0 DL0 CR1 ER1 DR0 HR1 EL1 ER0 AL1 AR1,RWL 5 2)::
(makeTM BR0 DL0 CR1 ER1 DL1 AR1 AL0 CL0 CR0 HR1,RWL 4 3)::
(makeTM BR0 DL0 CR1 ER1 DL1 EL0 AL0 CL1 HR1 AR0,RWL 5 2)::
(makeTM BR0 DR0 AL1 CL1 AR1 AL0 ER0 HR1 EL1 BL0,RWL 3 2)::
(makeTM BR0 DR0 CL0 HR1 DR1 BL1 EL0 CR0 AR1 EL1,RWL 2 2)::
(makeTM BR0 DR0 CL0 AR0 DL1 EL1 AR1 BL1 DL0 HR1,RWL 4 3)::
(makeTM BR0 DR0 CL0 AR1 BR1 CL1 HR1 ER1 CL0 ER1,RWL 2 2)::
(makeTM BR0 DR0 CL0 AR1 BR1 CL1 EL0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR0 DR0 CL0 AR1 BR1 CL1 EL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR0 DR0 CL0 AR1 BR1 CL1 EL0 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR0 DR0 CL0 AR1 DR1 HR1 EL0 DR1 BR1 EL1,RWL 2 2)::
(makeTM BR0 DR0 CL0 BR1 DL1 CL1 ER1 BR0 HR1 AR1,RWL 2 3)::
(makeTM BR0 DR0 CL0 EL0 DL1 ER0 AR1 BR0 BL1 HR1,RWL 4 2)::
(makeTM BR0 DR0 CL0 EL0 DR1 HR1 BL1 BR0 AR1 EL1,RWL 2 3)::
(makeTM BR0 DR0 CL0 EL0 DR1 HR1 BL1 DR1 AR1 EL1,RWL 2 3)::
(makeTM BR0 DR0 CL0 EL1 DR1 AR1 CL1 BL0 HR1 BL1,RWL 2 2)::
(makeTM BR0 DR0 CR0 BL0 DR1 HR1 EL1 AL1 AR1 DL0,RWL 9 2)::
(makeTM BR0 DR0 CR0 BR1 DL1 ER1 EL0 HR1 AR1 BL0,RWL 10 2)::
(makeTM BR0 DR0 CL1 HR1 AR1 AL0 BL0 ER1 CR1 HR1,RWL 2 3)::
(makeTM BR0 DR0 CL1 HR1 AR1 AL0 EL1 DR1 AL0 CL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 HR1 AR1 AL0 EL1 DR1 CL1 CL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 HR1 AR1 CL1 EL1 DR1 AL0 CL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 HR1 AR1 CL1 EL1 DR1 CL1 CL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 HR1 AR1 CL1 EL1 DR1 CR1 CL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 HR1 AR1 EL0 BL1 ER1 CR0 AL0,RWL 17 2)::
(makeTM BR0 DR0 CL1 HR1 DR1 EL0 CL1 DR1 AR1 EL1,RWL 2 3)::
(makeTM BR0 DR0 CL1 AL0 AR1 HR1 EL1 DR1 AL0 BL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 AL0 DR1 EL1 AL1 BR1 HR1 CL1,RWL 2 2)::
(makeTM BR0 DR0 CL1 AR0 DL0 AR1 ER1 CL0 DR1 HR1,RWL 10 2)::
(makeTM BR0 DR0 CL1 AR1 AR1 CL0 BL0 ER1 DR1 HR1,RWL 5 2)::
(makeTM BR0 DR0 CL1 AR1 DL0 BR1 ER0 BL0 CR1 HR1,RWL 3 2)::
(makeTM BR0 DR0 CL1 AR1 DL1 BL1 EL0 CL0 AR1 HR1,RWL 2 2)::
(makeTM BR0 DR0 CL1 AR1 DL1 EL0 BR1 CL0 AL0 HR1,RWL 57 2)::
(makeTM BR0 DR0 CL1 BL0 AR1 CL0 BR1 ER1 CR1 HR1,RWL 5 2)::
(makeTM BR0 DR0 CL1 BR0 AR1 DL1 EL1 CL1 CL0 HR1,RWL 2 3)::
(makeTM BR0 DR0 CL1 BL1 AR1 BL0 DL1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR0 DR0 CL1 BL1 AR1 EL1 DL1 CL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 DR0 CL1 BR1 AL1 AL0 ER1 BL1 HR1 CR1,RWL 2 2)::
(makeTM BR0 DR0 CL1 BR1 AL1 DL1 HR1 EL0 BR0 AL1,RWL 2 3)::
(makeTM BR0 DR0 CL1 BR1 AR1 CL1 EL1 CL0 DL0 HR1,RWL 1 4)::
(makeTM BR0 DR0 CL1 BR1 BR1 DR1 HR1 EL0 AR1 EL1,RWL 2 2)::
(makeTM BR0 DR0 CL1 CL0 AR1 AL0 BL1 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR0 DR0 CL1 CL0 AR1 CL1 BL1 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR0 DR0 CL1 CR1 AR1 CL0 DL0 ER1 CL1 HR1,RWL 6 3)::
(makeTM BR0 DR0 CL1 CR1 AR1 CL0 EL0 BR1 DL0 HR1,RWL 6 3)::
(makeTM BR0 DR0 CL1 CR1 BR1 AR1 DL1 ER0 HR1 BL0,RWL 5 2)::
(makeTM BR0 DR0 CL1 EL0 AR1 AL0 BL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 EL0 AR1 AL0 BL1 DR1 HR1 CL1,RWL 2 3)::
(makeTM BR0 DR0 CL1 EL0 AR1 AL1 BL1 CR0 BL1 HR1,RWL 3 2)::
(makeTM BR0 DR0 CL1 EL0 AR1 BL0 BR1 HR1 AL0 CR0,RWL 3 3)::
(makeTM BR0 DR0 CL1 EL0 AR1 BL0 ER1 HR1 BR1 ER0,RWL 2 3)::
(makeTM BR0 DR0 CL1 EL0 AR1 CL1 BL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 EL0 AR1 CL1 BL1 DR1 HR1 CL1,RWL 2 3)::
(makeTM BR0 DR0 CL1 EL0 AR1 ER1 BL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR0 DR0 CL1 EL0 DL1 HR1 ER1 BL0 DL1 AR0,RWL 3 2)::
(makeTM BR0 DR0 CL1 EL0 DL1 CL0 AR1 BL0 AL0 HR1,RWL 20 2)::
(makeTM BR0 DR0 CL1 EL0 DL1 CL0 AR1 BL0 CL0 HR1,RWL 4 2)::
(makeTM BR0 DR0 CL1 EL0 DL1 CL0 AR1 BL0 CR0 HR1,RWL 4 2)::
(makeTM BR0 DR0 CL1 ER0 AR1 CL0 BL1 DR1 HR1 CR1,RWL 21 2)::
(makeTM BR0 DR0 CL1 ER0 DL1 CL0 AR1 BL0 CL0 HR1,RWL 4 2)::
(makeTM BR0 DR0 CL1 EL1 DL1 CL0 AR1 BL0 AR1 HR1,RWL 4 2)::
(makeTM BR0 DR0 CL1 EL1 DL1 CL0 AR1 BL0 CR1 HR1,RWL 4 2)::
(makeTM BR0 DR0 CL1 ER1 AR1 CL0 BL0 CR1 BR1 HR1,RWL 5 2)::
(makeTM BR0 DR0 CL1 ER1 DL1 AR0 AR1 DL0 HR1 CR1,RWL 4 3)::
(makeTM BR0 DR0 CR1 HR1 DL1 EL0 CL1 DR1 AR1 EL1,RWL 2 3)::
(makeTM BR0 DR0 CR1 HR1 DR1 AL0 EL0 DL1 BR1 AL1,RWL 2 2)::
(makeTM BR0 DR0 CR1 HR1 DR1 CR0 EL0 AR1 AL0 EL1,RWL 6 2)::
(makeTM BR0 DR0 CR1 HR1 DR1 CR1 EL0 DL1 BR1 AL1,RWL 2 2)::
(makeTM BR0 DR0 CR1 HR1 DR1 EL0 CL1 DR1 AR1 EL1,RWL 2 3)::
(makeTM BR0 DR0 CR1 AR1 BL1 BR1 DL1 ER0 HR1 CL0,RWL 5 2)::
(makeTM BR0 DR0 CR1 BL1 DL1 AR0 BL1 EL0 CL0 HR1,RWL 3 3)::
(makeTM BR0 DR0 CR1 BR1 DL0 AL1 HR1 EL1 AL1 DL0,RWL 2 2)::
(makeTM BR0 DR0 CR1 BR1 DL0 AR1 HR1 EL1 AL1 CL0,RWL 3 3)::
(makeTM BR0 DR0 CR1 DL0 DR1 ER1 BL1 AL1 CR0 HR1,RWL 6 2)::
(makeTM BR0 DR0 CR1 DR1 DL1 HR1 EL1 AL1 AR1 DL0,RWL 9 2)::
(makeTM BR0 DR0 CR1 ER0 DL1 CL0 BR1 CL0 AR1 HR1,RWL 4 2)::
(makeTM BR0 DR0 CR1 ER1 AL1 CL1 CL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR0 DR0 CR1 ER1 DL0 AL0 AR1 CL1 BR1 HR1,RWL 6 2)::
(makeTM BR0 DL1 AL1 CL0 DR1 EL0 BR1 AL1 HR1 AR1,RWL 2 2)::
(makeTM BR0 DL1 AL1 CR0 BR1 ER0 EL0 HR1 CL1 BL0,RWL 6 2)::
(makeTM BR0 DL1 AL1 CR0 BR1 EL1 AL0 BR0 DL0 HR1,RWL 4 2)::
(makeTM BR0 DL1 AL1 CR0 BR1 EL1 AL0 DR0 DL0 HR1,RWL 4 2)::
(makeTM BR0 DL1 AL1 CL1 AR1 ER0 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 AL1 CL1 BR1 DR1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 AL1 CL1 DR1 HR1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 AL1 CR1 DR0 ER1 BL1 BL0 HR1 AR0,RWL 35 2)::
(makeTM BR0 DL1 CL0 HR1 BR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL0 AR1 AL1 HR1 ER1 EL0 BL0 ER1,RWL 13 2)::
(makeTM BR0 DL1 CL0 BR1 DR1 CR0 AL1 ER0 HR1 BL0,RWL 3 3)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 AL1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 AL1 EL1 HR1 BL0,RWL 3 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 BL0 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 BL0 EL0 HR1 DR1,RWL 2 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 BL0 EL1 HR1 AR0,RWL 3 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 BL0 EL1 HR1 BL0,RWL 3 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 BL1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 BL1 EL1 HR1 BL0,RWL 3 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 BR1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 BR1 EL1 HR1 BL0,RWL 3 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 CL1 EL1 HR1 BL0,RWL 3 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 CR1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 CR1 EL1 HR1 BL0,RWL 3 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 DR1 EL1 HR1 BL0,RWL 3 2)::
(makeTM BR0 DL1 CR0 BL1 AL1 CR1 ER1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR0 DL1 CR0 BR1 BL1 DR1 AL1 EL0 HR1 AL1,RWL 6 4)::
(makeTM BR0 DL1 CR0 BR1 DL0 DR1 AL1 EL1 HR1 CL0,RWL 3 3)::
(makeTM BR0 DL1 CR0 BR1 DL0 ER0 AL1 CL1 HR1 AR1,RWL 7 2)::
(makeTM BR0 DL1 CR0 BR1 DL1 ER0 AL1 DL0 HR1 DR0,RWL 15 2)::
(makeTM BR0 DL1 CR0 BR1 DR1 BL0 AL1 EL0 HR1 AL1,RWL 6 4)::
(makeTM BR0 DL1 CR0 BR1 DR1 DR1 AL1 EL0 HR1 AL1,RWL 6 4)::
(makeTM BR0 DL1 CL1 HR1 AR1 ER0 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 AR1 AR0 HR1 AL1 EL0 ER1 BL0,RWL 1 4)::
(makeTM BR0 DL1 CL1 AR1 AL1 HR1 AL1 EL0 ER1 BL0,RWL 1 4)::
(makeTM BR0 DL1 CL1 AR1 AL1 HR1 BL1 EL0 ER1 BL0,RWL 1 4)::
(makeTM BR0 DL1 CL1 AR1 AL1 HR1 EL1 EL0 ER1 BL0,RWL 1 4)::
(makeTM BR0 DL1 CL1 AR1 AL1 HR1 ER1 EL0 DR1 BL0,RWL 1 4)::
(makeTM BR0 DL1 CL1 AR1 AL1 HR1 ER1 EL0 ER1 BL0,RWL 1 4)::
(makeTM BR0 DL1 CL1 BR1 AR1 AL0 HR1 EL0 AR1 BR0,RWL 2 3)::
(makeTM BR0 DL1 CL1 BR1 AR1 ER0 HR1 CL0 AL0 EL1,RWL 2 3)::
(makeTM BR0 DL1 CL1 BR1 AR1 EL1 BR0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 BR1 AR1 EL1 BR0 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 BR1 DL1 EL1 BR0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 BR1 DL1 EL1 BR0 ER0 HR1 AL0,RWL 2 3)::
(makeTM BR0 DL1 CL1 BR1 DR1 EL1 BR0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 CR0 AL1 CR1 EL1 BL0 AL0 HR1,RWL 4 3)::
(makeTM BR0 DL1 CL1 CR0 AR1 DL0 EL1 AL1 CL0 HR1,RWL 2 3)::
(makeTM BR0 DL1 CL1 CR0 AR1 EL1 HR1 EL1 CL0 AL0,RWL 3 2)::
(makeTM BR0 DL1 CL1 CL1 BR1 DR1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 CR1 AL1 CR1 HR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 DL1 CL1 DR0 BR1 AL0 CL0 EL0 AR0 HR1,RWL 6 2)::
(makeTM BR0 DL1 CL1 DL1 BR1 ER0 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 DR1 CR1 BL1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 EL0 DR1 EL0 HR1 ER0 BR1 AL0,RWL 2 3)::
(makeTM BR0 DL1 CL1 ER0 AR1 HR1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 ER0 AR1 AR1 HR1 CL0 EL1 AL0,RWL 3 2)::
(makeTM BR0 DL1 CL1 ER0 AR1 CR0 HR1 CL0 EL1 AL0,RWL 3 2)::
(makeTM BR0 DL1 CL1 ER0 CR1 DL1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR0 DL1 CL1 ER1 AR1 AL0 ER0 AL1 HR1 BR1,RWL 2 3)::
(makeTM BR0 DL1 CR1 HR1 AL0 EL1 ER1 AR0 CL1 DR0,RWL 2 2)::
(makeTM BR0 DL1 CR1 HR1 AL1 CR1 AL0 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR0 DL1 CR1 HR1 AL1 CR1 CR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR0 DL1 CR1 HR1 AL1 CR1 EL1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR0 DL1 CR1 HR1 AL1 CR1 ER1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR0 DL1 CR1 HR1 AL1 DR0 AL0 ER1 AR1 EL0,RWL 5 2)::
(makeTM BR0 DL1 CR1 HR1 AL1 DR0 EL0 AL0 BR1 CL1,RWL 8 2)::
(makeTM BR0 DL1 CR1 HR1 DR1 AL0 ER1 DL0 AL0 AR1,RWL 5 2)::
(makeTM BR0 DL1 CR1 HR1 DR1 DL0 EL0 BR0 CL1 AL0,RWL 3 3)::
(makeTM BR0 DL1 CR1 AL0 AL1 AR1 CL1 EL0 HR1 BL1,RWL 4 2)::
(makeTM BR0 DL1 CR1 AL0 DR1 HR1 BL0 ER1 DL1 ER0,RWL 9 2)::
(makeTM BR0 DL1 CR1 AR0 AL1 BR0 EL1 HR1 AL0 BL0,RWL 3 2)::
(makeTM BR0 DL1 CR1 AR1 AL1 ER1 CR0 BL0 HR1 CR1,RWL 2 2)::
(makeTM BR0 DL1 CR1 AR1 DL1 BR0 BL1 EL0 CL0 HR1,RWL 4 2)::
(makeTM BR0 DL1 CR1 BL1 DL1 ER0 HR1 AL1 BL0 ER1,RWL 2 3)::
(makeTM BR0 DL1 CR1 BR1 CL1 AL1 HR1 EL1 CR0 ER0,RWL 2 2)::
(makeTM BR0 DL1 CR1 BR1 CL1 AL1 HR1 ER1 CL0 ER0,RWL 2 2)::
(makeTM BR0 DL1 CR1 BR1 CL1 AL1 HR1 ER1 CR0 ER0,RWL 2 2)::
(makeTM BR0 DL1 CR1 BR1 DL1 EL1 HR1 AL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 DL1 CR1 CL1 DL0 AR0 AL0 EL1 BL1 HR1,RWL 3 4)::
(makeTM BR0 DL1 CR1 DL0 AL0 DR0 EL1 AR0 BL1 HR1,RWL 4 2)::
(makeTM BR0 DL1 CR1 DL0 AL1 AR0 EL0 HR1 AR1 CR0,RWL 6 3)::
(makeTM BR0 DL1 CR1 DL0 AL1 AR0 EL0 HR1 AR1 EL0,RWL 6 3)::
(makeTM BR0 DL1 CR1 DL0 AL1 AR0 EL1 HR1 ER1 BR0,RWL 6 3)::
(makeTM BR0 DL1 CR1 DR0 AL0 ER1 CL1 BR1 HR1 AR1,RWL 2 3)::
(makeTM BR0 DL1 CR1 EL0 AL0 AR1 BL1 CR0 AL1 HR1,RWL 5 2)::
(makeTM BR0 DL1 CR1 EL0 AL1 AR0 AL1 HR1 BL1 EL0,RWL 5 3)::
(makeTM BR0 DL1 CR1 EL0 AL1 AR0 EL1 HR1 BL1 CL0,RWL 1 4)::
(makeTM BR0 DL1 CR1 EL0 AL1 BR0 CL1 HR1 BL1 CL1,RWL 2 3)::
(makeTM BR0 DL1 CR1 ER0 AL1 BR0 BL1 HR1 EL1 DL0,RWL 14 2)::
(makeTM BR0 DL1 CR1 ER1 AL0 CR0 EL1 HR1 AL1 CL0,RWL 3 2)::
(makeTM BR0 DL1 CR1 ER1 AL0 EL0 AL1 HR1 CL1 CR0,RWL 4 3)::
(makeTM BR0 DL1 CR1 ER1 AL1 AR1 AR1 DL0 HR1 BR1,RWL 5 2)::
(makeTM BR0 DL1 CR1 ER1 AL1 CL1 AL0 CR0 HR1 DR0,RWL 5 3)::
(makeTM BR0 DL1 CR1 ER1 DR0 HR1 AL1 BL0 AL0 AR1,RWL 6 3)::
(makeTM BR0 DL1 CR1 ER1 DR0 AR1 DL1 BL1 HR1 DL0,RWL 5 2)::
(makeTM BR0 DL1 CR1 ER1 DR1 AR1 AL1 BL1 HR1 DL0,RWL 5 2)::
(makeTM BR0 DR1 AL1 CL1 DL0 AR1 ER1 CL0 CR0 HR1,RWL 4 2)::
(makeTM BR0 DR1 CL0 HR1 DL1 DL0 AR1 ER0 CR1 BL1,RWL 5 3)::
(makeTM BR0 DR1 CL0 AR0 DL1 EL1 AR1 ER0 HR1 BL0,RWL 5 2)::
(makeTM BR0 DR1 CL0 AR1 BR1 CL1 HR1 ER0 CL0 ER1,RWL 3 2)::
(makeTM BR0 DR1 CL0 AR1 BR1 CL1 DL1 EL1 HR1 CL0,RWL 2 3)::
(makeTM BR0 DR1 CL0 CR1 DL1 HR1 ER1 DL0 AR0 AR1,RWL 10 2)::
(makeTM BR0 DR1 CL0 EL0 DL1 HR1 AR1 BL1 AR0 DL0,RWL 6 2)::
(makeTM BR0 DR1 CL0 ER0 DL1 BL1 AR1 BL1 HR1 CR1,RWL 8 2)::
(makeTM BR0 DR1 CR0 EL0 DL0 CR0 EL1 HR1 AR1 BL1,RWL 2 3)::
(makeTM BR0 DR1 CL1 HR1 AR1 CL0 EL1 AR0 CR1 EL1,RWL 2 3)::
(makeTM BR0 DR1 CL1 HR1 CR1 AL1 CL0 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR0 DR1 CL1 HR1 DL1 DR0 ER0 BL0 CR1 AR0,RWL 3 3)::
(makeTM BR0 DR1 CL1 AL0 AR1 HR1 BL1 ER0 BL0 ER1,RWL 2 2)::
(makeTM BR0 DR1 CL1 AL0 DL0 AR1 ER1 CL0 CR0 HR1,RWL 4 2)::
(makeTM BR0 DR1 CL1 AR0 AR1 DL1 EL0 CR0 HR1 BL1,RWL 4 2)::
(makeTM BR0 DR1 CL1 AR1 DL1 EL0 BR1 BL0 HR1 DL0,RWL 4 2)::
(makeTM BR0 DR1 CL1 BL0 DL0 AR1 ER1 CL0 CR0 HR1,RWL 4 2)::
(makeTM BR0 DR1 CL1 BL1 AR1 CR1 BL0 ER0 HR1 AR1,RWL 3 2)::
(makeTM BR0 DR1 CL1 BL1 AR1 CR1 BL0 ER1 HR1 AR0,RWL 3 2)::
(makeTM BR0 DR1 CL1 CL0 AR1 EL1 CL0 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 DR1 CL1 CL0 AR1 EL1 CL0 DL1 HR1 CL0,RWL 2 2)::
(makeTM BR0 DR1 CL1 CL0 AR1 EL1 CL0 DL1 HR1 DR0,RWL 2 2)::
(makeTM BR0 DR1 CL1 CL1 DL0 AR1 ER1 CL0 CR0 HR1,RWL 4 2)::
(makeTM BR0 DR1 CL1 DL0 DL0 AR1 ER1 CL0 CR0 HR1,RWL 4 2)::
(makeTM BR0 DR1 CL1 DR1 DL0 AR1 ER1 CL0 CR0 HR1,RWL 4 2)::
(makeTM BR0 DR1 CL1 EL0 AR1 BL0 BR1 HR1 CL0 DR0,RWL 28 2)::
(makeTM BR0 DR1 CL1 EL0 AR1 BL0 BR1 HR1 ER1 DR0,RWL 14 2)::
(makeTM BR0 DR1 CL1 EL0 DL0 AR1 ER1 CL0 CR0 HR1,RWL 4 2)::
(makeTM BR0 DR1 CL1 EL0 DR1 AR0 BL0 CR0 BL1 HR1,RWL 4 2)::
(makeTM BR0 DR1 CL1 EL1 AR1 BL0 ER0 HR1 BR1 CR0,RWL 8 2)::
(makeTM BR0 DR1 CL1 EL1 AR1 DR0 BL0 CL0 HR1 BL1,RWL 2 2)::
(makeTM BR0 DR1 CR1 HR1 DL0 AR0 AR1 EL1 DR1 EL0,RWL 10 2)::
(makeTM BR0 DR1 CR1 HR1 DR0 CR0 DL1 EL1 AR1 EL0,RWL 2 3)::
(makeTM BR0 DR1 CR1 HR1 DL1 CL0 ER1 CL0 AR1 DR0,RWL 2 3)::
(makeTM BR0 DR1 CR1 HR1 DL1 DR0 AR1 EL1 CL0 EL0,RWL 4 2)::
(makeTM BR0 DR1 CR1 HR1 DL1 ER1 AR1 CL0 ER0 AL0,RWL 7 2)::
(makeTM BR0 DR1 CR1 AL0 DL1 AR1 ER1 CL0 HR1 BR1,RWL 4 2)::
(makeTM BR0 DR1 CR1 AR1 DL1 BR1 HR1 EL1 AL1 EL0,RWL 2 4)::
(makeTM BR0 DR1 CR1 BL1 AL1 ER1 BL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR0 DR1 CR1 CL0 BL1 AL1 AR1 ER1 DR0 HR1,RWL 10 2)::
(makeTM BR0 DR1 CR1 CL0 BL1 DL0 HR1 EL0 ER1 AR0,RWL 2 3)::
(makeTM BR0 DR1 CR1 DL1 AL1 AR0 BL1 EL0 HR1 CR0,RWL 3 2)::
(makeTM BR0 DR1 CR1 EL0 AL1 AR0 HR1 ER1 BL1 CL0,RWL 11 3)::
(makeTM BR0 DR1 CR1 EL0 AL1 AR0 CL0 DL1 BL1 HR1,RWL 7 2)::
(makeTM BR0 DR1 CR1 EL0 DL1 CR1 EL1 BL1 HR1 AL0,RWL 2 3)::
(makeTM BR0 DR1 CR1 EL0 DR1 CR1 BL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 DR1 CR1 ER0 DL1 AL1 AR1 CL0 DL0 HR1,RWL 2 4)::
(makeTM BR0 DR1 CR1 ER1 DL0 CL1 AR1 BL1 HR1 AR0,RWL 3 3)::
(makeTM BR0 EL0 AL1 CL1 CR1 DR0 DL1 AL0 HR1 BR0,RWL 2 2)::
(makeTM BR0 EL0 AL1 CL1 DR0 CL1 BR1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 AL1 CR1 DL1 BR1 BL1 DR0 HR1 CL0,RWL 2 3)::
(makeTM BR0 EL0 CL0 HR1 DR0 AL0 ER1 AR1 CL1 DR1,RWL 3 3)::
(makeTM BR0 EL0 CL0 HR1 DL1 CR1 CR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CL0 HR1 DL1 CR1 EL1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CL0 HR1 DL1 CR1 ER1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CL0 HR1 DR1 DR0 AL1 DR1 CR1 EL1,RWL 2 3)::
(makeTM BR0 EL0 CL0 BR1 DR1 CL1 BL1 ER1 HR1 AR1,RWL 3 2)::
(makeTM BR0 EL0 CL0 BR1 DR1 CL1 BR1 ER1 HR1 AR1,RWL 3 2)::
(makeTM BR0 EL0 CL0 BR1 DR1 CL1 CL1 ER1 HR1 AR1,RWL 3 2)::
(makeTM BR0 EL0 CR0 HR1 DL0 BR1 ER1 EL1 CR1 AL0,RWL 12 2)::
(makeTM BR0 EL0 CR0 HR1 DL1 CR1 BL1 AL1 AL0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DL1 CR1 BL1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DL1 CR1 CR1 AL1 AL0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DL1 CR1 CR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DL1 CR1 EL1 AL1 AL0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DL1 CR1 EL1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DL1 CR1 ER1 AL1 AL0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DL1 CR1 ER1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DR1 CR1 AL0 DL1 CL1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 HR1 DR1 DR0 AL1 DR1 CR1 EL1,RWL 2 3)::
(makeTM BR0 EL0 CR0 AR1 DL0 BR1 CR1 DL1 HR1 BL1,RWL 21 2)::
(makeTM BR0 EL0 CR0 BL1 DR0 CR1 EL1 HR1 AL1 BL0,RWL 2 2)::
(makeTM BR0 EL0 CR0 BL1 DR1 CR1 DL1 AL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 EL0 CR0 BL1 DR1 CR1 EL1 BL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 BR1 DL1 AL0 AL1 HR1 CR0 CL1,RWL 5 2)::
(makeTM BR0 EL0 CR0 BR1 DL1 AL0 AL1 HR1 ER1 CL1,RWL 3 3)::
(makeTM BR0 EL0 CR0 BR1 DL1 CL0 AL1 DL1 HR1 BL0,RWL 2 2)::
(makeTM BR0 EL0 CR0 BR1 DL1 CL1 AL1 CL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 BR1 DL1 CL1 AL1 CR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CR0 DR1 DL0 HR1 AL1 AR1 DL1 DR0,RWL 5 2)::
(makeTM BR0 EL0 CR0 ER1 DL0 AL0 EL1 HR1 BR1 CL1,RWL 6 2)::
(makeTM BR0 EL0 CL1 HR1 DR1 AL1 CL1 DR1 DR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CL1 AR1 DL1 HR1 ER1 AL0 BL0 BR0,RWL 15 2)::
(makeTM BR0 EL0 CL1 BL0 DR1 BR0 AL1 CR0 BL1 HR1,RWL 2 3)::
(makeTM BR0 EL0 CL1 BL1 DR1 AL1 BR1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CL1 BR1 AL1 DL0 HR1 BR0 BR0 EL1,RWL 3 2)::
(makeTM BR0 EL0 CL1 BR1 AL1 DL0 HR1 CR1 BR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CL1 BR1 AL1 DR0 CR1 DR0 AL0 HR1,RWL 28 3)::
(makeTM BR0 EL0 CL1 BR1 AL1 DL1 HR1 AL0 CR0 CR1,RWL 2 3)::
(makeTM BR0 EL0 CL1 BR1 AL1 DL1 HR1 AR0 BR0 EL1,RWL 3 2)::
(makeTM BR0 EL0 CL1 BR1 AL1 DL1 HR1 AL1 BR0 EL1,RWL 3 2)::
(makeTM BR0 EL0 CL1 BR1 AL1 DR1 HR1 BR0 ER1 CR1,RWL 2 2)::
(makeTM BR0 EL0 CL1 BR1 AL1 DR1 DL1 AR1 HR1 CL0,RWL 3 3)::
(makeTM BR0 EL0 CL1 BR1 AL1 DR1 EL0 AR1 HR1 CL0,RWL 3 3)::
(makeTM BR0 EL0 CL1 BR1 BR1 DL1 HR1 AL1 BR0 EL1,RWL 3 2)::
(makeTM BR0 EL0 CL1 BR1 CR1 DL1 HR1 AL1 BR0 EL1,RWL 3 2)::
(makeTM BR0 EL0 CL1 BR1 DL0 AL0 AR1 BR0 HR1 BR0,RWL 2 3)::
(makeTM BR0 EL0 CL1 BR1 DL0 AL0 AR1 BR0 HR1 CR1,RWL 2 3)::
(makeTM BR0 EL0 CL1 BR1 DL1 AL0 ER1 AR1 HR1 BR0,RWL 2 3)::
(makeTM BR0 EL0 CL1 BR1 DL1 AL0 ER1 CR0 HR1 BR0,RWL 2 3)::
(makeTM BR0 EL0 CL1 BR1 DL1 AL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 EL0 CL1 BR1 DL1 CR0 EL1 HR1 AL1 AL0,RWL 9 2)::
(makeTM BR0 EL0 CL1 BR1 DL1 CR0 EL1 HR1 AL1 CL1,RWL 3 2)::
(makeTM BR0 EL0 CL1 BR1 DR1 AL0 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 EL0 CL1 CR0 DL0 AL0 AR1 BR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CL1 CR0 DL0 AL0 AR1 BR1 HR1 AR1,RWL 2 2)::
(makeTM BR0 EL0 CL1 CR0 DL0 AL0 AR1 BR1 HR1 CR0,RWL 2 2)::
(makeTM BR0 EL0 CL1 CR0 DL1 AL0 AR1 AL0 HR1 AR1,RWL 2 2)::
(makeTM BR0 EL0 CL1 CR0 DL1 AL0 AR1 BL1 HR1 AR1,RWL 1 4)::
(makeTM BR0 EL0 CL1 CR0 DR1 CL0 AL1 DR0 BL0 HR1,RWL 4 3)::
(makeTM BR0 EL0 CL1 CR1 DR1 AL0 HR1 BR1 ER1 BR0,RWL 3 2)::
(makeTM BR0 EL0 CL1 CR1 DR1 AL1 HR1 BL1 ER1 BR0,RWL 2 2)::
(makeTM BR0 EL0 CL1 DL0 AL1 HR1 AR1 AR0 BR1 EL1,RWL 2 3)::
(makeTM BR0 EL0 CL1 DL0 DL1 ER1 BR1 AL1 HR1 BR0,RWL 3 2)::
(makeTM BR0 EL0 CL1 DL0 DR1 AR0 BL1 CR0 AL0 HR1,RWL 8 2)::
(makeTM BR0 EL0 CL1 DR0 AL1 HR1 DR1 AR1 CL0 DL1,RWL 5 2)::
(makeTM BR0 EL0 CL1 DR0 AL1 AR0 BR1 CR1 BL1 HR1,RWL 6 3)::
(makeTM BR0 EL0 CL1 DR0 AL1 CR1 HR1 CR1 BR1 EL1,RWL 2 3)::
(makeTM BR0 EL0 CL1 DR0 BR1 AL1 DL1 AL0 HR1 BR1,RWL 2 3)::
(makeTM BR0 EL0 CL1 DR0 DL1 HR1 ER1 AL0 CR0 BR0,RWL 14 2)::
(makeTM BR0 EL0 CL1 DR1 AL1 BL0 CL1 AR1 HR1 CR0,RWL 3 2)::
(makeTM BR0 EL0 CL1 DR1 AL1 CR1 HR1 BR1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CL1 DR1 CR1 BL1 HR1 AL1 ER1 BR0,RWL 2 2)::
(makeTM BR0 EL0 CL1 ER1 DL0 HR1 AL1 AL0 AR1 CR0,RWL 4 3)::
(makeTM BR0 EL0 CL1 ER1 DL0 ER0 AL1 HR1 BL1 AR0,RWL 6 2)::
(makeTM BR0 EL0 CR1 HR1 DL0 ER0 AR1 EL1 DR1 CL0,RWL 6 2)::
(makeTM BR0 EL0 CR1 HR1 DR0 ER0 DL1 AL0 CR1 BL0,RWL 5 3)::
(makeTM BR0 EL0 CR1 HR1 DL1 CR0 AR1 AL0 DL0 BR1,RWL 6 2)::
(makeTM BR0 EL0 CR1 HR1 DL1 DR1 AR1 EL0 CL1 BR0,RWL 5 2)::
(makeTM BR0 EL0 CR1 HR1 DR1 AR0 AL0 DR0 DL0 EL1,RWL 7 2)::
(makeTM BR0 EL0 CR1 HR1 DR1 AL1 CL1 DR1 DR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR1 HR1 DR1 CR1 EL0 DL1 BR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CR1 HR1 DR1 DR0 EL1 AR1 CL0 AL0,RWL 4 3)::
(makeTM BR0 EL0 CR1 AL0 DL1 DR1 HR1 BL1 ER1 BR0,RWL 3 2)::
(makeTM BR0 EL0 CR1 AR1 DL0 BR1 AL0 DL1 HR1 CL1,RWL 7 2)::
(makeTM BR0 EL0 CR1 AR1 DL1 AR1 AL0 CL1 HR1 BL1,RWL 8 2)::
(makeTM BR0 EL0 CR1 BR0 DR1 CL1 AL1 AR1 HR1 DL0,RWL 2 3)::
(makeTM BR0 EL0 CR1 BL1 BL0 DR1 CR1 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CR1 BL1 DR0 DR1 AL1 BR0 HR1 BL0,RWL 2 3)::
(makeTM BR0 EL0 CR1 BL1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR1 BR1 DR0 CL1 DL1 AL1 HR1 DL1,RWL 3 2)::
(makeTM BR0 EL0 CR1 BR1 DL1 AR1 AL1 CL1 HR1 CL0,RWL 10 3)::
(makeTM BR0 EL0 CR1 BR1 DL1 AR1 AL1 CL1 HR1 DL1,RWL 5 2)::
(makeTM BR0 EL0 CR1 BR1 DL1 CL1 AL1 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR0 EL0 CR1 BR1 DL1 CL1 AL1 AL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CR1 BR1 DL1 CL1 BL0 AL1 HR1 DL1,RWL 3 2)::
(makeTM BR0 EL0 CR1 BR1 DL1 CL1 BR1 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR0 EL0 CR1 BR1 DL1 CL1 BR1 AL1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL0 CR1 BR1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR0 EL0 CR1 BR1 DR1 BR0 AL1 BL0 HR1 DL0,RWL 6 2)::
(makeTM BR0 EL0 CR1 BR1 DR1 CL1 AL1 AR1 HR1 DL0,RWL 2 3)::
(makeTM BR0 EL0 CR1 BR1 DR1 DL0 AL1 DL1 HR1 BR0,RWL 2 2)::
(makeTM BR0 EL0 CR1 BR1 DR1 DR0 AL1 BL0 HR1 DL0,RWL 1 4)::
(makeTM BR0 EL0 CR1 BR1 DR1 ER1 AL1 BL0 HR1 DL0,RWL 3 3)::
(makeTM BR0 EL0 CR1 DR0 DL1 AL0 HR1 BL1 ER1 BR0,RWL 3 2)::
(makeTM BR0 EL0 CR1 DR1 CL1 BL1 HR1 AL0 ER1 BR0,RWL 3 2)::
(makeTM BR0 EL0 CR1 DR1 DR1 HR1 AL1 ER0 BL0 AR1,RWL 8 2)::
(makeTM BR0 EL0 CR1 ER0 DL1 HR1 EL0 EL1 AR1 DL1,RWL 10 2)::
(makeTM BR0 EL0 CR1 EL1 DR1 ER0 EL1 HR1 AR1 BL1,RWL 4 3)::
(makeTM BR0 ER0 AL1 CL1 DL0 AR0 DR1 BR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 ER0 AL1 CL1 DL0 AR0 DR1 BR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 ER0 CL0 HR1 DL1 AR1 ER1 AL0 CL1 CR1,RWL 6 3)::
(makeTM BR0 ER0 CL0 HR1 DL1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR0 ER0 CL0 AR1 DL1 HR1 BR1 DL1 DL0 ER1,RWL 2 2)::
(makeTM BR0 ER0 CL0 BR1 DL1 AR1 AL1 DL0 HR1 CR0,RWL 2 3)::
(makeTM BR0 ER0 CL0 BR1 DL1 CL1 DR1 AL1 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER0 CL0 BR1 DL1 CL1 ER0 AL1 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER0 CL0 BR1 DL1 CL1 ER0 BR1 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER0 CL0 BR1 DR1 CL1 BL0 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 ER0 CL0 BR1 DR1 CL1 BL0 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR0 ER0 CL0 BR1 DR1 CL1 CL0 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 ER0 CL0 BR1 DR1 CL1 CL0 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR0 ER0 CL0 BR1 DR1 CL1 EL0 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR0 ER0 CL0 DL0 BR1 CL1 AR1 DR1 HR1 BR0,RWL 2 3)::
(makeTM BR0 ER0 CL0 DR1 AL1 EL1 BR1 HR1 AR1 AL0,RWL 4 3)::
(makeTM BR0 ER0 CL0 ER1 DL1 HR1 AR1 BL1 DR1 EL0,RWL 7 2)::
(makeTM BR0 ER0 CR0 HR1 DL1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR0 ER0 CL1 HR1 DL0 AL0 ER1 CL1 AR1 DR1,RWL 2 2)::
(makeTM BR0 ER0 CL1 HR1 DL0 AR1 ER1 CL0 CR0 DR0,RWL 6 2)::
(makeTM BR0 ER0 CL1 HR1 DR0 EL0 AR1 EL1 CR1 DL1,RWL 4 3)::
(makeTM BR0 ER0 CL1 HR1 DL1 BL1 AR0 CL0 DR1 AR1,RWL 5 2)::
(makeTM BR0 ER0 CL1 HR1 DL1 CL1 AR1 CL0 CR1 DR0,RWL 1 3)::
(makeTM BR0 ER0 CL1 AL0 DL0 HR1 DR1 ER0 AL1 BR1,RWL 2 2)::
(makeTM BR0 ER0 CL1 BR0 DL1 HR1 EL1 CL0 AR1 DL0,RWL 2 3)::
(makeTM BR0 ER0 CL1 BR1 AL1 DL1 HR1 AL0 CL0 AL0,RWL 2 3)::
(makeTM BR0 ER0 CL1 BR1 AL1 DL1 HR1 AL0 CL0 CL1,RWL 2 2)::
(makeTM BR0 ER0 CL1 BR1 DL1 EL1 CR1 AL1 HR1 DL0,RWL 2 3)::
(makeTM BR0 ER0 CL1 BR1 DL1 ER1 AR1 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 ER0 CL1 BR1 DR1 ER1 AR1 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR0 ER0 CL1 CL0 DR1 AL0 HR1 ER0 BL1 ER1,RWL 2 3)::
(makeTM BR0 ER0 CL1 DL0 CR1 BL1 AR1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 ER0 CL1 DL0 DL0 HR1 AR1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR0 ER0 CL1 DL0 DL0 HR1 AR1 DL1 BL1 ER1,RWL 2 3)::
(makeTM BR0 ER0 CL1 DL0 DL0 AR0 CR1 DL1 HR1 BR0,RWL 2 4)::
(makeTM BR0 ER0 CL1 DL0 DR1 AR0 HR1 BR1 EL1 BL0,RWL 3 2)::
(makeTM BR0 ER0 CL1 DR0 AL1 BL0 DL1 AR1 HR1 BR1,RWL 2 3)::
(makeTM BR0 ER0 CL1 DR0 DL0 AL0 AR1 CL0 BL1 HR1,RWL 8 2)::
(makeTM BR0 ER0 CL1 DL1 CR1 BR1 HR1 AR0 EL1 BL0,RWL 3 2)::
(makeTM BR0 ER0 CL1 DR1 DL1 HR1 EL1 CL0 AR1 DL0,RWL 4 2)::
(makeTM BR0 ER0 CL1 DR1 DL1 AL0 BR1 CL0 AR1 HR1,RWL 8 2)::
(makeTM BR0 ER0 CL1 EL0 DL0 HR1 AR1 DL1 CR0 BR0,RWL 2 3)::
(makeTM BR0 ER0 CL1 ER0 DL0 HR1 EL1 BR0 AR1 CL0,RWL 5 3)::
(makeTM BR0 ER0 CL1 ER0 DL1 CL1 BR1 DR1 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER0 CL1 EL1 DL1 CL1 BR1 DR1 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER0 CL1 ER1 DL1 CL1 BR1 DR1 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER0 CR1 HR1 DL1 AL0 ER1 CL0 AL0 BR1,RWL 9 2)::
(makeTM BR0 ER0 CR1 HR1 DL1 AR1 AL0 CL1 DL0 CR0,RWL 6 2)::
(makeTM BR0 ER0 CR1 HR1 DL1 EL0 AR1 CL0 DL1 DL0,RWL 3 3)::
(makeTM BR0 ER0 CR1 AR1 DL0 HR1 BR1 EL1 DL1 BL0,RWL 2 2)::
(makeTM BR0 ER0 CR1 BR0 DL1 BL0 AR1 CL0 BR1 HR1,RWL 2 3)::
(makeTM BR0 ER0 CR1 BR1 DL1 AR0 AL1 CL1 HR1 CL0,RWL 4 4)::
(makeTM BR0 ER0 CR1 BR1 DL1 AR0 BL1 DL1 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER0 CR1 BR1 DL1 AL1 BL1 DL1 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER0 CR1 BR1 DL1 CL1 HR1 AL1 CL0 ER1,RWL 2 2)::
(makeTM BR0 ER0 CR1 CL1 DL1 AR0 HR1 BL1 EL1 BL0,RWL 3 2)::
(makeTM BR0 ER0 CR1 CL1 DL1 AR1 HR1 BR1 EL1 BL0,RWL 2 2)::
(makeTM BR0 ER0 CR1 DL1 BL0 AR1 EL1 HR1 AR1 EL0,RWL 6 2)::
(makeTM BR0 ER0 CR1 DL1 CL1 BR1 HR1 AR1 EL1 BL0,RWL 2 2)::
(makeTM BR0 ER0 CR1 DR1 CL1 AL1 HR1 BR1 CL0 ER0,RWL 2 2)::
(makeTM BR0 ER0 CR1 DR1 CL1 AL1 HR1 BR1 CR0 ER0,RWL 2 2)::
(makeTM BR0 ER0 CR1 DR1 DL1 AR1 AL1 CL0 HR1 CL1,RWL 2 3)::
(makeTM BR0 ER0 CR1 EL0 DL1 AL0 AL0 CL0 AR1 HR1,RWL 4 2)::
(makeTM BR0 ER0 CR1 ER1 DL1 HR1 AL1 DL0 DR1 BR1,RWL 2 3)::
(makeTM BR0 EL1 AL1 CL0 DR1 CL1 BR1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL1 AL1 CL0 DR1 DL0 BR1 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL1 AL1 CL1 CR1 DR0 DL1 AL0 HR1 BR0,RWL 2 2)::
(makeTM BR0 EL1 AL1 CL1 CR1 DR0 DL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR0 EL1 AL1 CL1 CR1 DR0 DL1 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR0 EL1 AL1 CL1 CR1 DR0 DL1 AL0 HR1 DR0,RWL 2 2)::
(makeTM BR0 EL1 AL1 CL1 DR0 CL1 BR1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 AL1 CL1 DR1 CL0 DR1 BR1 HR1 AL1,RWL 2 2)::
(makeTM BR0 EL1 AL1 CL1 DR1 ER0 BR0 BR1 HR1 DL0,RWL 2 2)::
(makeTM BR0 EL1 AL1 CR1 DR1 HR1 EL1 DR0 BL0 DL0,RWL 6 2)::
(makeTM BR0 EL1 CL0 AR0 DL1 HR1 AL1 AL0 BR1 BL0,RWL 7 2)::
(makeTM BR0 EL1 CL0 AR0 DL1 BL1 AL1 HR1 BR1 CL0,RWL 4 2)::
(makeTM BR0 EL1 CL0 AR0 DL1 BL1 AL1 HR1 BR1 CR0,RWL 4 2)::
(makeTM BR0 EL1 CL0 AR1 DL1 HR1 BR1 AL0 BL1 ER0,RWL 5 2)::
(makeTM BR0 EL1 CL0 BR1 DR1 CL1 EL1 BR0 HR1 AL1,RWL 2 3)::
(makeTM BR0 EL1 CL0 DR1 AL1 DL0 AR1 CL1 HR1 BL1,RWL 2 3)::
(makeTM BR0 EL1 CR0 HR1 DR1 DL1 ER1 AR0 CL1 EL0,RWL 2 3)::
(makeTM BR0 EL1 CR0 BL1 DL1 DR1 AL1 DR1 HR1 BL0,RWL 2 2)::
(makeTM BR0 EL1 CL1 HR1 DR0 CL1 AL1 DR1 AL0 CL0,RWL 2 2)::
(makeTM BR0 EL1 CL1 HR1 DR0 CL1 AL1 DR1 CL1 CL0,RWL 2 2)::
(makeTM BR0 EL1 CL1 HR1 DR0 CL1 AL1 DR1 CR1 CL0,RWL 2 2)::
(makeTM BR0 EL1 CL1 HR1 DR0 CL1 AL1 DR1 DR1 CL0,RWL 2 2)::
(makeTM BR0 EL1 CL1 AR0 DL1 BL0 EL1 HR1 BR1 EL0,RWL 6 2)::
(makeTM BR0 EL1 CL1 AR0 DL1 CR0 AL1 HR1 BR1 CL0,RWL 3 2)::
(makeTM BR0 EL1 CL1 AR1 DL1 HR1 AR1 AL0 BL1 DL0,RWL 7 2)::
(makeTM BR0 EL1 CL1 BR0 DL0 AL1 DR1 BR1 HR1 CL0,RWL 12 2)::
(makeTM BR0 EL1 CL1 BR1 AL1 DL1 HR1 AL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 EL1 CL1 BR1 BR1 DL1 HR1 AL0 BR0 EL1,RWL 2 2)::
(makeTM BR0 EL1 CL1 BR1 DL0 AL0 AR1 BR0 HR1 CR0,RWL 2 3)::
(makeTM BR0 EL1 CL1 BR1 DL0 AL0 AR1 BR0 HR1 DL0,RWL 2 3)::
(makeTM BR0 EL1 CL1 BR1 DL0 AL0 AR1 DL1 HR1 BR0,RWL 3 2)::
(makeTM BR0 EL1 CL1 CR0 DR1 AL0 HR1 BR1 DR0 AL1,RWL 2 3)::
(makeTM BR0 EL1 CL1 CR0 DR1 AL0 HR1 BR1 DR0 CR0,RWL 2 3)::
(makeTM BR0 EL1 CL1 CR1 AL1 DR0 CR0 BL0 AL0 HR1,RWL 7 3)::
(makeTM BR0 EL1 CL1 CR1 AL1 DR0 EL0 CR0 AL0 HR1,RWL 12 2)::
(makeTM BR0 EL1 CL1 CR1 CR1 DR0 DL1 AL0 HR1 AL1,RWL 2 3)::
(makeTM BR0 EL1 CL1 DR0 AL1 HR1 AR1 DL1 CL1 DL0,RWL 5 2)::
(makeTM BR0 EL1 CL1 DR0 AL1 HR1 BL0 AR1 AR1 EL0,RWL 9 2)::
(makeTM BR0 EL1 CL1 DR0 AL1 CL1 CR1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CL1 DR0 BR1 HR1 DL1 AL0 HR1 AL1,RWL 2 3)::
(makeTM BR0 EL1 CL1 DR0 CR1 DR0 DL1 AL0 HR1 AL1,RWL 2 3)::
(makeTM BR0 EL1 CL1 DL1 AL1 AL0 DR1 AR0 BL0 HR1,RWL 9 2)::
(makeTM BR0 EL1 CL1 DL1 AL1 CL1 DR1 AR0 BL0 HR1,RWL 9 2)::
(makeTM BR0 EL1 CL1 DL1 DL1 HR1 ER1 AL0 BL0 AR0,RWL 8 2)::
(makeTM BR0 EL1 CL1 DR1 AL1 AL0 HR1 BR1 DR0 AL1,RWL 2 3)::
(makeTM BR0 EL1 CL1 DR1 AL1 AL0 HR1 BR1 DR0 CR0,RWL 2 3)::
(makeTM BR0 EL1 CL1 DR1 AL1 BL0 CL1 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR0 EL1 CL1 DR1 AL1 CL0 AR1 DR1 HR1 CR1,RWL 3 3)::
(makeTM BR0 EL1 CL1 DR1 DR1 AL0 HR1 BR1 DR0 AL1,RWL 2 3)::
(makeTM BR0 EL1 CL1 DR1 DR1 AL0 HR1 BR1 DR0 CR0,RWL 2 3)::
(makeTM BR0 EL1 CL1 ER1 DR1 AL0 HR1 BL0 BR1 CR0,RWL 3 2)::
(makeTM BR0 EL1 CL1 ER1 DR1 AL0 HR1 BR1 BR1 CR0,RWL 3 2)::
(makeTM BR0 EL1 CR1 HR1 DL1 AR1 AL0 EL0 CL1 ER0,RWL 7 2)::
(makeTM BR0 EL1 CR1 HR1 DL1 DR0 BL0 AL0 AR1 CL1,RWL 2 3)::
(makeTM BR0 EL1 CR1 HR1 DL1 DR0 BL0 AL0 CL1 HR1,RWL 2 3)::
(makeTM BR0 EL1 CR1 AL0 DL1 AR0 BL1 CL1 AL0 HR1,RWL 9 2)::
(makeTM BR0 EL1 CR1 AR0 DL1 HR1 DR1 EL0 DL0 AR1,RWL 2 2)::
(makeTM BR0 EL1 CR1 BL0 DR0 CR0 DL1 AL1 HR1 CL1,RWL 2 2)::
(makeTM BR0 EL1 CR1 BL0 DR0 CR0 DL1 AL1 HR1 CR1,RWL 2 2)::
(makeTM BR0 EL1 CR1 BR0 DR1 EL0 AL1 ER0 HR1 BL0,RWL 2 3)::
(makeTM BR0 EL1 CR1 BL1 DR1 CR1 AL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 BR1 DL0 AR1 HR1 EL1 AL1 CL0,RWL 35 2)::
(makeTM BR0 EL1 CR1 BR1 DR0 HR1 DL1 AL1 CR0 ER0,RWL 3 2)::
(makeTM BR0 EL1 CR1 BR1 DR0 CL1 DL1 AL1 HR1 DL0,RWL 3 2)::
(makeTM BR0 EL1 CR1 BR1 DL1 CL1 AL1 AL0 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 BR1 DL1 CL1 AL1 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 BR1 DL1 CL1 AL1 AR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 BR1 DL1 CL1 BL0 AL1 HR1 DL0,RWL 3 2)::
(makeTM BR0 EL1 CR1 BR1 DL1 CL1 BR1 AL0 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 BR1 DL1 CL1 BR1 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 BR1 DL1 CL1 BR1 AR1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 CL0 DL1 CR0 AL0 AL1 BL1 HR1,RWL 38 2)::
(makeTM BR0 EL1 CR1 CR0 DL1 AR0 AL0 DL1 DL0 HR1,RWL 35 2)::
(makeTM BR0 EL1 CR1 CR0 DL1 CR1 HR1 EL0 BR1 AL1,RWL 2 3)::
(makeTM BR0 EL1 CR1 CR0 DR1 CR1 AL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 CL1 DL1 CR0 BL0 AR0 AL0 HR1,RWL 12 3)::
(makeTM BR0 EL1 CR1 CR1 DL1 AR0 BL1 CL1 AL0 HR1,RWL 9 2)::
(makeTM BR0 EL1 CR1 DL1 DR0 EL1 BL1 AL0 HR1 BL0,RWL 8 2)::
(makeTM BR0 EL1 CR1 DL1 DR1 AL0 BL1 CR0 BL0 HR1,RWL 8 2)::
(makeTM BR0 EL1 CR1 DR1 DR1 AR1 AL1 EL0 HR1 BL1,RWL 5 2)::
(makeTM BR0 EL1 CR1 ER0 DR1 CR1 AL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 EL1 CR1 EL1 DR1 CR1 BL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR0 ER1 CL0 AR1 DL1 DR1 AR0 BL0 CR1 HR1,RWL 3 4)::
(makeTM BR0 ER1 CL0 BR1 DL1 CL1 ER1 BR0 HR1 AR1,RWL 2 3)::
(makeTM BR0 ER1 CL0 BR1 DR1 CL1 BL0 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR0 ER1 CL0 BR1 DR1 CL1 BL0 AR1 HR1 DL0,RWL 3 2)::
(makeTM BR0 ER1 CL0 BR1 DR1 CL1 CL0 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR0 ER1 CL0 BR1 DR1 CL1 CL0 AR1 HR1 DL0,RWL 3 2)::
(makeTM BR0 ER1 CL0 DR1 AL1 HR1 EL1 BL0 AR1 DL0,RWL 2 2)::
(makeTM BR0 ER1 CL1 AL0 DL1 HR1 BR1 BL0 AR1 BR1,RWL 3 2)::
(makeTM BR0 ER1 CL1 AR1 DL0 AL1 BR1 BL0 HR1 BR1,RWL 3 2)::
(makeTM BR0 ER1 CL1 BL0 DL1 ER0 AR1 EL0 HR1 BR0,RWL 2 3)::
(makeTM BR0 ER1 CL1 BL0 DR1 CR0 AR1 DL1 HR1 BR1,RWL 10 2)::
(makeTM BR0 ER1 CL1 BR0 DL0 HR1 ER0 BL0 AR1 EL0,RWL 4 2)::
(makeTM BR0 ER1 CL1 BR0 DL0 HR1 EL1 BL0 AR1 AR0,RWL 2 2)::
(makeTM BR0 ER1 CL1 BR1 DL0 AR1 DR1 CL0 BR0 HR1,RWL 4 2)::
(makeTM BR0 ER1 CL1 BR1 DL0 CR1 AR1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR0 ER1 CL1 BR1 DL1 CL1 AR0 BR0 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER1 CL1 BR1 DL1 CL1 AR1 BR0 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER1 CL1 CL0 DL1 HR1 DR1 AL1 BL1 AR0,RWL 6 2)::
(makeTM BR0 ER1 CL1 CR1 DL1 AR1 ER1 CL0 HR1 BR1,RWL 4 2)::
(makeTM BR0 ER1 CL1 CR1 DR1 CL0 AR1 DL1 HR1 CL1,RWL 2 4)::
(makeTM BR0 ER1 CL1 DL0 DL0 AR0 AR1 DL1 HR1 CL0,RWL 2 3)::
(makeTM BR0 ER1 CL1 DL0 DL0 AR0 CR1 DL1 HR1 CL0,RWL 2 4)::
(makeTM BR0 ER1 CL1 DL0 DL0 CR1 AR1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR0 ER1 CL1 DR0 DL0 AL0 AR1 CL0 CL1 HR1,RWL 8 2)::
(makeTM BR0 ER1 CL1 DL1 BR1 AR0 AL0 CL0 HR1 AR1,RWL 2 2)::
(makeTM BR0 ER1 CL1 DR1 AL1 HR1 EL1 AR1 BL1 DL0,RWL 13 2)::
(makeTM BR0 ER1 CL1 DR1 AL1 AL0 HR1 BR1 CR0 CL1,RWL 2 2)::
(makeTM BR0 ER1 CL1 DR1 AL1 AL0 HR1 BR1 CR0 DL0,RWL 2 2)::
(makeTM BR0 ER1 CL1 DR1 AL1 CL1 HR1 BR0 BR1 ER1,RWL 2 2)::
(makeTM BR0 ER1 CL1 DR1 AL1 CL1 HR1 BR0 CL0 ER1,RWL 2 2)::
(makeTM BR0 ER1 CL1 ER0 DL1 HR1 AL1 BL1 AR1 DL0,RWL 4 2)::
(makeTM BR0 ER1 CR1 HR1 DL0 CL0 DR1 ER0 CL1 AR1,RWL 2 3)::
(makeTM BR0 ER1 CR1 HR1 DR1 CL0 ER0 DL1 CL1 AR1,RWL 11 2)::
(makeTM BR0 ER1 CR1 HR1 DR1 CR1 EL1 EL0 AR1 DL0,RWL 4 3)::
(makeTM BR0 ER1 CR1 AL0 DL1 AR1 AR0 CL0 DR1 HR1,RWL 5 2)::
(makeTM BR0 ER1 CR1 AR1 DL1 CL1 HR1 EL0 AL1 BL0,RWL 2 4)::
(makeTM BR0 ER1 CR1 BR1 DL1 DL0 AR1 CL1 HR1 CR0,RWL 2 4)::
(makeTM BR0 ER1 CR1 CL0 DL0 ER0 BL1 CL1 AR0 HR1,RWL 12 2)::
(makeTM BR0 ER1 CR1 CL0 DL1 HR1 BL0 AR0 BL1 DR0,RWL 4 3)::
(makeTM BR0 ER1 CR1 CR1 DL1 AR1 ER1 CL0 HR1 BR1,RWL 4 2)::
(makeTM BR0 ER1 CR1 DL0 DR1 CR0 BL1 AL1 HR1 AR0,RWL 6 2)::
(makeTM BR0 ER1 CR1 DR0 DL1 HR1 AR1 EL1 DL0 BL0,RWL 2 3)::
(makeTM BR0 ER1 CR1 DR1 CL1 AL1 HR1 BR1 CL0 ER0,RWL 2 2)::
(makeTM BR0 ER1 CR1 DR1 CL1 AL1 HR1 BR1 CR0 ER0,RWL 2 2)::
(makeTM BR0 ER1 CR1 DR1 CL1 AL1 HR1 BR1 CL1 ER0,RWL 2 2)::
(makeTM BR0 ER1 CR1 DR1 DL1 BR0 AR1 CL0 DR1 HR1,RWL 2 3)::
(makeTM BR0 ER1 CR1 EL1 DL1 AR0 HR1 BL1 BL0 CL0,RWL 3 2)::
(makeTM BR1 HR1 BL1 CL0 DL0 ER0 DR1 BR1 CR1 AR0,RWL 4 3)::
(makeTM BR1 HR1 BL1 CR0 BR0 DL1 EL0 CR0 AL1 DL0,RWL 3 3)::
(makeTM BR1 HR1 BL1 CR0 BR0 DL1 EL0 CR1 AL1 DL0,RWL 2 2)::
(makeTM BR1 HR1 BL1 CL1 AL1 DL0 DR1 ER0 BR0 CR1,RWL 2 2)::
(makeTM BR1 HR1 BL1 CL1 DL0 BR0 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 HR1 BL1 CR1 AL0 DL1 BR0 EL0 ER1 CR0,RWL 2 2)::
(makeTM BR1 HR1 BL1 CR1 AR1 DR1 EL1 DR0 BL0 CL0,RWL 2 3)::
(makeTM BR1 HR1 BL1 CR1 DL1 CR0 EL1 HR1 BL0 AL0,RWL 2 2)::
(makeTM BR1 HR1 BL1 CR1 DL1 CR0 EL1 EL1 BL0 AL1,RWL 2 2)::
(makeTM BR1 HR1 CL0 AR0 DL1 CR1 ER1 EL0 BL0 CR0,RWL 4 2)::
(makeTM BR1 HR1 CL0 AR1 EL1 DL1 ER1 EL0 BR0 DR0,RWL 4 3)::
(makeTM BR1 HR1 CL0 BL0 CR1 DR0 BL1 ER1 AR0 DR1,RWL 2 3)::
(makeTM BR1 HR1 CL0 BR0 EL0 DL1 BL0 BL1 ER1 AR0,RWL 2 3)::
(makeTM BR1 HR1 CL0 BR0 ER1 DL0 EL0 DL1 AR1 EL0,RWL 23 2)::
(makeTM BR1 HR1 CL0 BR1 DR1 CL1 HR1 ER1 BL1 BR0,RWL 2 2)::
(makeTM BR1 HR1 CL0 BR1 DR1 CL1 HR1 ER1 BR1 BR0,RWL 2 2)::
(makeTM BR1 HR1 CL0 BR1 DR1 CL1 HR1 ER1 CL1 BR0,RWL 2 2)::
(makeTM BR1 HR1 CL0 BR1 DR1 CL1 AL0 ER1 DR0 BR0,RWL 2 2)::
(makeTM BR1 HR1 CL0 CR0 DR1 BL1 ER0 AR1 EL1 AL1,RWL 4 2)::
(makeTM BR1 HR1 CL0 CR0 DR1 DL1 ER1 DL0 AR0 AR1,RWL 10 2)::
(makeTM BR1 HR1 CL0 CL1 DR1 BL1 ER0 CL0 AR1 CR0,RWL 10 2)::
(makeTM BR1 HR1 CL0 CR1 DL1 BR0 ER0 DL0 CL1 ER1,RWL 2 3)::
(makeTM BR1 HR1 CL0 DL0 EL0 DR1 BL1 AR0 ER1 AR0,RWL 4 2)::
(makeTM BR1 HR1 CL0 DL0 EL0 DR1 BL1 AR0 ER1 CL1,RWL 4 3)::
(makeTM BR1 HR1 CL0 DL0 EL0 DR1 BL1 CR1 ER1 AR0,RWL 4 2)::
(makeTM BR1 HR1 CL0 DR0 DL0 CL1 AR1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 HR1 CL0 DR0 DL1 DR1 EL1 BR0 AL1 BL1,RWL 4 3)::
(makeTM BR1 HR1 CL0 DR0 EL1 DR1 BL1 CR1 AL0 DL0,RWL 4 3)::
(makeTM BR1 HR1 CL0 DR0 ER1 DL1 CR1 BL0 AR0 DL0,RWL 6 2)::
(makeTM BR1 HR1 CL0 DL1 CR1 DR0 AL1 ER0 HR1 BL1,RWL 2 2)::
(makeTM BR1 HR1 CL0 DL1 ER1 AL1 CL1 EL0 BL1 CR0,RWL 4 2)::
(makeTM BR1 HR1 CL0 DR1 AR0 BL1 EL1 ER0 CR0 EL1,RWL 13 2)::
(makeTM BR1 HR1 CL0 DR1 AL1 DL1 EL1 DR0 BL1 ER1,RWL 2 4)::
(makeTM BR1 HR1 CL0 DR1 AR1 BL1 BR1 ER0 EL1 CR0,RWL 1 4)::
(makeTM BR1 HR1 CL0 DR1 AR1 BL1 CR1 ER0 EL1 CR0,RWL 1 4)::
(makeTM BR1 HR1 CL0 DR1 AR1 BL1 EL1 ER0 DL1 CR0,RWL 1 4)::
(makeTM BR1 HR1 CL0 DR1 AR1 BL1 EL1 ER0 EL1 CR0,RWL 1 4)::
(makeTM BR1 HR1 CL0 DR1 AR1 BL1 ER1 ER0 EL1 CR0,RWL 1 4)::
(makeTM BR1 HR1 CL0 EL0 AR1 DL1 EL1 CL1 BR0 DR0,RWL 2 2)::
(makeTM BR1 HR1 CL0 ER0 AL1 DL1 BR1 BL1 DR1 AL0,RWL 5 2)::
(makeTM BR1 HR1 CL0 ER0 AL1 DL1 BR1 BL1 DR1 DL0,RWL 5 2)::
(makeTM BR1 HR1 CL0 ER0 DL0 CL1 AR1 BR0 DR1 DR1,RWL 3 3)::
(makeTM BR1 HR1 CL0 ER0 DL0 CL1 AR1 BR0 EL1 DR1,RWL 3 3)::
(makeTM BR1 HR1 CL0 ER0 DL0 CR1 EL0 DL1 AR1 CR0,RWL 2 2)::
(makeTM BR1 HR1 CL0 ER0 DL1 CL1 EL0 DR1 AR0 BR1,RWL 2 2)::
(makeTM BR1 HR1 CL0 ER0 ER1 DL1 CR1 DL0 AR0 CR1,RWL 10 2)::
(makeTM BR1 HR1 CL0 EL1 AR0 DL1 ER1 CR0 BL1 DR0,RWL 2 2)::
(makeTM BR1 HR1 CL0 EL1 AR1 DR0 ER1 BL0 BL1 CL1,RWL 4 2)::
(makeTM BR1 HR1 CL0 EL1 AR1 DL1 ER1 BL1 CR1 DR0,RWL 13 2)::
(makeTM BR1 HR1 CL0 EL1 AR1 DL1 ER1 CR0 BL1 DR0,RWL 2 2)::
(makeTM BR1 HR1 CL0 ER1 AR1 DL0 CR0 BL1 BL1 ER0,RWL 9 2)::
(makeTM BR1 HR1 CL0 ER1 DL0 CL1 AR1 BR0 DR0 EL1,RWL 3 2)::
(makeTM BR1 HR1 CL0 ER1 DR0 BL0 AR1 CR1 CL1 DL0,RWL 4 2)::
(makeTM BR1 HR1 CL0 ER1 DR0 BL0 AR1 CR1 CL1 DR0,RWL 4 2)::
(makeTM BR1 HR1 CL0 ER1 DR1 BL0 AR1 BR0 CL1 DR0,RWL 23 2)::
(makeTM BR1 HR1 CL0 ER1 DR1 BL0 AR1 DL0 CL1 DR0,RWL 3 2)::
(makeTM BR1 HR1 CR0 AR0 CL1 DR1 EL1 DL0 BR1 ER1,RWL 4 3)::
(makeTM BR1 HR1 CR0 AR0 DL1 ER1 EL1 BL0 CR1 DL0,RWL 8 2)::
(makeTM BR1 HR1 CR0 AR0 DR1 AL0 EL1 BL0 BL0 DL0,RWL 4 2)::
(makeTM BR1 HR1 CR0 BL0 DL1 ER0 EL1 AL1 CR1 BR1,RWL 3 3)::
(makeTM BR1 HR1 CR0 BR0 CL1 DL0 AL1 EL1 DL1 ER0,RWL 2 3)::
(makeTM BR1 HR1 CR0 BR0 CL1 DL1 ER1 DL0 AR0 CR1,RWL 2 3)::
(makeTM BR1 HR1 CR0 BR0 CL1 DR1 BL1 EL1 AL1 EL0,RWL 2 3)::
(makeTM BR1 HR1 CR0 BR0 DR0 ER1 DL1 EL0 AL0 BL1,RWL 3 2)::
(makeTM BR1 HR1 CR0 BL1 DL1 CR1 BL1 EL1 AL0 BL0,RWL 2 2)::
(makeTM BR1 HR1 CR0 BL1 DL1 CR1 BR1 EL1 AL0 BL0,RWL 2 2)::
(makeTM BR1 HR1 CR0 BL1 DL1 CR1 CL1 EL1 AL0 BL0,RWL 2 2)::
(makeTM BR1 HR1 CR0 BL1 DL1 CR1 CR1 EL1 AL0 BL0,RWL 2 2)::
(makeTM BR1 HR1 CR0 BL1 DL1 CR1 EL1 ER0 AL0 BL0,RWL 2 2)::
(makeTM BR1 HR1 CR0 BL1 DL1 CR1 EL1 EL1 AL0 BL0,RWL 2 2)::
(makeTM BR1 HR1 CR0 BL1 DL1 CR1 ER1 EL1 AL0 BL0,RWL 2 2)::
(makeTM BR1 HR1 CR0 BR1 DL1 BR0 EL0 AL1 BR1 CL0,RWL 8 2)::
(makeTM BR1 HR1 CR0 BR1 DL1 EL1 CL0 AR0 DR1 EL0,RWL 15 2)::
(makeTM BR1 HR1 CR0 BR1 DR1 DR0 EL1 BL0 AL1 DL0,RWL 4 2)::
(makeTM BR1 HR1 CR0 CL0 DL1 AR1 EL0 DL0 AL0 BL1,RWL 7 2)::
(makeTM BR1 HR1 CR0 CL0 DL1 AR1 EL0 DL0 ER1 BL1,RWL 7 2)::
(makeTM BR1 HR1 CR0 CL0 DR1 EL0 CL1 AR0 AR1 BL1,RWL 8 2)::
(makeTM BR1 HR1 CR0 CL1 DR0 EL1 DL1 AL0 BL0 BL1,RWL 4 2)::
(makeTM BR1 HR1 CR0 CL1 DR0 EL1 DL1 AL0 BL0 BR1,RWL 5 2)::
(makeTM BR1 HR1 CR0 CL1 DR0 EL1 DL1 AL0 BL0 CL1,RWL 5 2)::
(makeTM BR1 HR1 CR0 CL1 DR0 EL1 DL1 AL0 BL0 EL1,RWL 5 2)::
(makeTM BR1 HR1 CR0 CR1 DL1 AR0 EL0 DL0 BR1 BL0,RWL 12 2)::
(makeTM BR1 HR1 CR0 DL0 AL1 AR0 CL0 EL1 CR1 BL0,RWL 4 3)::
(makeTM BR1 HR1 CR0 DL0 DR1 EL0 BL1 AR1 CL1 ER1,RWL 1 3)::
(makeTM BR1 HR1 CR0 DL0 DR1 EL0 ER1 AR0 CL1 DL0,RWL 19 2)::
(makeTM BR1 HR1 CR0 DR0 DL0 AR1 EL1 CL0 CR1 DL0,RWL 3 2)::
(makeTM BR1 HR1 CR0 DR0 DL1 BR0 EL0 AL1 BR1 CL0,RWL 8 2)::
(makeTM BR1 HR1 CR0 DR0 DR1 EL0 ER1 AR1 CL1 DL0,RWL 4 2)::
(makeTM BR1 HR1 CR0 DL1 DR0 AL0 EL0 BL1 AL1 EL0,RWL 2 3)::
(makeTM BR1 HR1 CR0 DR1 DR0 EL0 ER1 AR1 CL1 DL0,RWL 6 2)::
(makeTM BR1 HR1 CR0 EL0 DR1 CL1 BL1 ER0 AR1 CL0,RWL 13 2)::
(makeTM BR1 HR1 CR0 EL0 DR1 ER1 BL1 BR0 DL1 AR0,RWL 8 2)::
(makeTM BR1 HR1 CR0 ER0 CL1 DL0 AR0 EL0 BR1 AL0,RWL 5 3)::
(makeTM BR1 HR1 CR0 ER0 CL1 DL0 ER0 EL0 BR1 AL0,RWL 5 3)::
(makeTM BR1 HR1 CR0 ER0 CL1 DL1 EL0 ER1 AR1 BR0,RWL 2 2)::
(makeTM BR1 HR1 CR0 ER0 DL1 AL1 EL1 DL0 BR1 CL0,RWL 4 2)::
(makeTM BR1 HR1 CR0 ER0 DL1 BR1 EL1 CL1 AL0 DL0,RWL 2 2)::
(makeTM BR1 HR1 CR0 ER0 DR1 AR0 EL1 DL0 CR1 DL0,RWL 4 2)::
(makeTM BR1 HR1 CR0 EL1 DL1 BR0 BL0 CL0 AL0 DL0,RWL 6 2)::
(makeTM BR1 HR1 CR0 EL1 DL1 BR0 DL1 BL1 AL0 BL0,RWL 7 2)::
(makeTM BR1 HR1 CR0 ER1 DL1 BR0 EL0 ER0 AR0 CL0,RWL 15 2)::
(makeTM BR1 HR1 CR0 ER1 DL1 EL0 CL0 BL1 AR1 DR0,RWL 1 4)::
(makeTM BR1 HR1 CL1 AL0 EL1 DL1 BL1 ER0 DR1 CL0,RWL 2 3)::
(makeTM BR1 HR1 CL1 AL0 ER1 DL1 BL0 ER0 DL0 CR0,RWL 5 2)::
(makeTM BR1 HR1 CL1 AL0 ER1 DR1 ER0 DL0 BL1 CR0,RWL 3 3)::
(makeTM BR1 HR1 CL1 AR1 BL0 DL1 ER1 CL0 CR0 ER0,RWL 4 2)::
(makeTM BR1 HR1 CL1 AR1 BR1 DR0 CR1 EL1 DL0 CL0,RWL 6 2)::
(makeTM BR1 HR1 CL1 AR1 DL0 CR0 ER1 BL0 BR0 HR1,RWL 6 2)::
(makeTM BR1 HR1 CL1 AR1 DR1 CL0 BR0 ER0 BL0 CR1,RWL 5 2)::
(makeTM BR1 HR1 CL1 BL0 DR1 BL0 ER1 CR0 AR0 CR1,RWL 2 3)::
(makeTM BR1 HR1 CL1 BR0 AL0 DL1 ER1 CL0 BL1 ER1,RWL 2 3)::
(makeTM BR1 HR1 CL1 BR0 DL0 AL1 DL1 EL0 AR1 AR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 BR0 DL0 BL0 EL1 AR0 DR1 BL1,RWL 9 2)::
(makeTM BR1 HR1 CL1 BR0 DL0 BL0 EL1 AR1 DR0 CL1,RWL 6 2)::
(makeTM BR1 HR1 CL1 BR0 DL0 DL1 EL0 AR0 CR1 BL1,RWL 12 2)::
(makeTM BR1 HR1 CL1 BR0 DL0 DL1 EL0 BL1 AR0 AL1,RWL 10 2)::
(makeTM BR1 HR1 CL1 BR0 DL1 AL1 EL0 HR1 EL1 BR1,RWL 2 2)::
(makeTM BR1 HR1 CL1 BR0 DL1 AL1 ER0 EL0 CL0 CR0,RWL 6 2)::
(makeTM BR1 HR1 CL1 BR0 DL1 DL1 EL0 AL1 AR0 CL0,RWL 3 3)::
(makeTM BR1 HR1 CL1 BR0 DR1 DL0 AR0 EL0 CL0 AR1,RWL 6 2)::
(makeTM BR1 HR1 CL1 BR0 EL0 DL0 DR0 AL1 BR1 BL1,RWL 6 3)::
(makeTM BR1 HR1 CL1 BR0 ER0 DL1 EL0 DR1 AR1 CL0,RWL 3 2)::
(makeTM BR1 HR1 CL1 BR0 EL1 DL0 AR1 CL1 DR1 EL0,RWL 16 2)::
(makeTM BR1 HR1 CL1 BR0 ER1 DL0 CR1 CL0 AR1 DR0,RWL 6 2)::
(makeTM BR1 HR1 CL1 BL1 DR0 CL0 EL0 DR1 AL1 CR0,RWL 1 3)::
(makeTM BR1 HR1 CL1 BL1 DR0 CR1 AL1 ER0 BL0 DR1,RWL 2 2)::
(makeTM BR1 HR1 CL1 BL1 DR0 CR1 AL1 ER0 BR1 DR1,RWL 2 2)::
(makeTM BR1 HR1 CL1 BL1 DR0 CR1 AL1 ER0 DR0 DR1,RWL 2 2)::
(makeTM BR1 HR1 CL1 BL1 ER0 DL0 AL1 CR0 DR0 ER1,RWL 1 3)::
(makeTM BR1 HR1 CL1 BL1 EL1 DR0 CR1 EL0 DL1 AL1,RWL 4 4)::
(makeTM BR1 HR1 CL1 BR1 HR1 DL0 ER1 DL1 BL1 BR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 BR1 HR1 DL0 ER1 DL1 BR1 BR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 BR1 HR1 DL1 BR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 HR1 CL1 BR1 HR1 DL1 EL1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 HR1 CL1 BR1 HR1 DL1 ER1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 HR1 CL1 BR1 AL0 DL0 ER1 DL1 CR0 BR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 BR1 AR0 DL1 CL0 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 HR1 CL1 CL0 AL1 DL0 DR1 ER0 BR0 CR1,RWL 4 2)::
(makeTM BR1 HR1 CL1 CL0 DR1 BL0 CR1 ER0 EL0 AR1,RWL 2 3)::
(makeTM BR1 HR1 CL1 CL0 DR1 BL0 DR1 ER0 EL0 AR1,RWL 2 3)::
(makeTM BR1 HR1 CL1 CL0 ER1 DR0 BL0 DL1 ER0 AR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 CR0 HR1 DL0 EL1 BR1 ER1 DR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 CR0 AL0 DL0 AR0 EL1 BL1 HR1,RWL 2 3)::
(makeTM BR1 HR1 CL1 CR0 AL0 DL0 AR0 EL1 DR1 BL1,RWL 2 3)::
(makeTM BR1 HR1 CL1 CR0 AL0 DL0 ER1 DL1 BR1 BR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 CR0 AL0 DL0 ER1 DL1 CR0 BR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 CR0 DL1 BL0 DR0 ER0 EL1 AL1,RWL 2 3)::
(makeTM BR1 HR1 CL1 CR0 DR1 CL0 ER0 ER1 BL0 AR1,RWL 38 2)::
(makeTM BR1 HR1 CL1 CR0 DR1 DL1 EL0 DL0 AL1 AR1,RWL 4 2)::
(makeTM BR1 HR1 CL1 CR0 EL0 DR1 ER0 BR0 AR1 CL1,RWL 7 2)::
(makeTM BR1 HR1 CL1 CR0 ER0 DL0 BL1 DR0 AR1 EL0,RWL 4 2)::
(makeTM BR1 HR1 CL1 CR0 ER1 DL0 AR1 BL0 BL1 AR0,RWL 3 4)::
(makeTM BR1 HR1 CL1 CR0 ER1 DL0 AR1 BL0 BR1 AR0,RWL 3 4)::
(makeTM BR1 HR1 CL1 CR0 ER1 DL0 AR1 BL1 DR1 BR0,RWL 1 4)::
(makeTM BR1 HR1 CL1 CR0 ER1 DL0 AR1 BL1 DR1 EL0,RWL 1 3)::
(makeTM BR1 HR1 CL1 CR0 ER1 DL0 ER1 BL0 BR1 AR0,RWL 3 4)::
(makeTM BR1 HR1 CL1 CR0 ER1 DL1 BL0 DL0 AR0 CR1,RWL 4 2)::
(makeTM BR1 HR1 CL1 CR1 AR0 DL0 EL1 CL0 ER1 DR0,RWL 3 3)::
(makeTM BR1 HR1 CL1 CR1 DL0 CL0 ER0 AR0 DR1 AL0,RWL 2 2)::
(makeTM BR1 HR1 CL1 CR1 DL1 CL0 DR1 ER0 BR1 AR1,RWL 3 3)::
(makeTM BR1 HR1 CL1 CR1 ER0 DL0 BL0 ER1 DR0 AR1,RWL 3 4)::
(makeTM BR1 HR1 CL1 CR1 ER0 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 HR1 CL1 CR1 EL1 DR1 AL1 DR0 AL1 BL0,RWL 5 2)::
(makeTM BR1 HR1 CL1 CR1 EL1 DR1 DL1 BR0 AR1 EL0,RWL 5 3)::
(makeTM BR1 HR1 CL1 CR1 ER1 DL0 BL1 AR0 AR0 DL0,RWL 5 2)::
(makeTM BR1 HR1 CL1 CR1 ER1 DL0 BL1 AR0 DR0 DL0,RWL 5 2)::
(makeTM BR1 HR1 CL1 CR1 ER1 DL0 BL1 AR0 DR1 DL0,RWL 5 2)::
(makeTM BR1 HR1 CL1 DL0 AR1 DR1 EL1 BL1 CR0 ER1,RWL 5 2)::
(makeTM BR1 HR1 CL1 DL0 AR1 DR1 ER1 BL1 CR0 DL1,RWL 2 3)::
(makeTM BR1 HR1 CL1 DL0 AR1 DR1 ER1 BL1 CR0 EL1,RWL 2 3)::
(makeTM BR1 HR1 CL1 DL0 BL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 DL0 DR0 BL0 ER1 DL1 ER0 AR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 DL0 EL0 AL1 AR0 BR0 ER1 DL1,RWL 2 3)::
(makeTM BR1 HR1 CL1 DL0 EL1 DR1 CR1 DR0 AL0 BL0,RWL 6 2)::
(makeTM BR1 HR1 CL1 DR0 AR0 DL1 CL0 ER1 CR1 EL0,RWL 5 2)::
(makeTM BR1 HR1 CL1 DR0 AR0 DL1 EL0 CL0 AR1 BL1,RWL 8 2)::
(makeTM BR1 HR1 CL1 DR0 AR1 DL0 EL0 BR1 CR1 EL0,RWL 4 3)::
(makeTM BR1 HR1 CL1 DR0 AR1 DL1 ER1 CL0 CR0 EL0,RWL 4 2)::
(makeTM BR1 HR1 CL1 DR0 BR1 CL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 HR1 CL1 DR0 DL0 DL1 ER1 AL0 BR0 EL0,RWL 6 2)::
(makeTM BR1 HR1 CL1 DR0 ER0 DL0 EL0 CR1 AR1 BR1,RWL 8 2)::
(makeTM BR1 HR1 CL1 DR0 EL1 DR1 AR1 BR0 BL1 DL0,RWL 1 3)::
(makeTM BR1 HR1 CL1 DR0 ER1 DL0 AR1 EL0 BL0 CR1,RWL 2 2)::
(makeTM BR1 HR1 CL1 DR0 ER1 DL0 AR1 EL0 BL0 DR1,RWL 2 2)::
(makeTM BR1 HR1 CL1 DL1 BR0 CL0 EL0 DR0 AR1 AL0,RWL 12 2)::
(makeTM BR1 HR1 CL1 DL1 DR1 BL0 AL1 ER0 CL1 BR1,RWL 9 2)::
(makeTM BR1 HR1 CL1 DL1 ER1 DL0 CR1 BL1 AL0 ER0,RWL 3 3)::
(makeTM BR1 HR1 CL1 DR1 AL1 BL0 ER0 ER1 BR1 DL0,RWL 6 2)::
(makeTM BR1 HR1 CL1 DR1 BR1 CL1 HR1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 HR1 CL1 DR1 CR0 DL0 AR1 EL0 CL0 BL0,RWL 1 4)::
(makeTM BR1 HR1 CL1 DR1 CR0 DL0 AR1 EL0 CR0 BL0,RWL 1 4)::
(makeTM BR1 HR1 CL1 DR1 CR1 BR0 EL1 ER0 HR1 BL0,RWL 2 3)::
(makeTM BR1 HR1 CL1 DR1 DL0 AL1 EL0 BR0 AR0 EL0,RWL 2 3)::
(makeTM BR1 HR1 CL1 DR1 DL0 BR0 EL1 BR1 AL0 BL0,RWL 4 3)::
(makeTM BR1 HR1 CL1 DR1 DL0 BR0 EL1 BR1 AL1 BL0,RWL 4 3)::
(makeTM BR1 HR1 CL1 DR1 DL0 BL1 AR0 ER0 CL0 BR0,RWL 6 2)::
(makeTM BR1 HR1 CL1 DR1 EL0 DL0 AR1 CL0 ER1 BR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 DR1 EL0 DL1 BR0 ER0 AL1 BL0,RWL 2 3)::
(makeTM BR1 HR1 CL1 DR1 ER1 DL0 CL0 BR0 DR0 AR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 EL0 AL0 DR1 HR1 BL1 ER1 CR0,RWL 2 2)::
(makeTM BR1 HR1 CL1 EL0 BL0 DL0 AR1 BR0 DR1 DL1,RWL 2 3)::
(makeTM BR1 HR1 CL1 EL0 DL0 BL0 ER1 EL0 ER1 AR0,RWL 12 2)::
(makeTM BR1 HR1 CL1 EL0 DL0 BL1 DR1 EL1 AR0 BR0,RWL 5 2)::
(makeTM BR1 HR1 CL1 EL0 DL0 CL1 DR1 EL1 AR0 BR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 EL0 DR0 DL0 BL1 ER1 AR1 AR0,RWL 1 4)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 HR1 AR1 ER1 AR0,RWL 14 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 AR0 ER0 CL1 CL0,RWL 3 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 BL0 CR1 ER1 AR0,RWL 3 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 BR0 AR0 DL0 CR0,RWL 3 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 BR0 AR1 CL0 AR0,RWL 28 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 BR1 AR1 ER1 DR0,RWL 14 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 BR1 CR1 ER1 AR0,RWL 3 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 BR1 DR1 ER1 AR0,RWL 14 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 CR1 AR1 DL0 AR0,RWL 5 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 DR0 AR0 DR1 CL1,RWL 2 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 DR0 AR0 DR1 EL1,RWL 2 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 DR0 AR1 DL0 AR0,RWL 5 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 DL1 CR1 ER1 AR0,RWL 3 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 DR1 AR1 DL0 AR0,RWL 5 3)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 EL0 AR1 AR0 DR0,RWL 9 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 EL0 AR1 CR1 AR0,RWL 14 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 EL0 ER0 CR1 AR0,RWL 14 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 EL1 CR1 AL0 ER0,RWL 2 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 ER1 AR1 CR1 AR0,RWL 14 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 ER1 CR1 AR0 BR1,RWL 2 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 CL0 BL1 AR1 CL1 AR0,RWL 7 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 CL1 ER1 DL0 AR1 CR0,RWL 2 4)::
(makeTM BR1 HR1 CL1 ER0 AL0 DL0 AR1 BL0 BR0 BR1,RWL 4 2)::
(makeTM BR1 HR1 CL1 ER0 AL0 DL0 AR1 EL1 BL0 CR0,RWL 17 2)::
(makeTM BR1 HR1 CL1 ER0 BR0 DL1 EL0 DR1 AR1 CL0,RWL 3 2)::
(makeTM BR1 HR1 CL1 ER0 BL1 DL0 AL1 DL1 CR0 BR0,RWL 2 2)::
(makeTM BR1 HR1 CL1 ER0 DL0 DR1 AR1 BL0 BL1 CR0,RWL 7 2)::
(makeTM BR1 HR1 CL1 ER0 DR0 CL0 BL1 DR1 AR0 BR1,RWL 4 3)::
(makeTM BR1 HR1 CL1 ER0 DR0 CL0 BL1 DR1 AR0 EL0,RWL 4 3)::
(makeTM BR1 HR1 CL1 ER0 DR0 CL0 BL1 DR1 AR1 BR1,RWL 2 4)::
(makeTM BR1 HR1 CL1 ER0 DR0 DL0 AR1 EL1 DL0 CR0,RWL 15 2)::
(makeTM BR1 HR1 CL1 ER0 DL1 DL0 AL1 BL1 CR0 CR1,RWL 3 3)::
(makeTM BR1 HR1 CL1 ER0 DR1 CL0 BL1 AR0 CR0 BL0,RWL 3 3)::
(makeTM BR1 HR1 CL1 ER0 DR1 CL0 EL0 AR0 CR0 CL1,RWL 3 3)::
(makeTM BR1 HR1 CL1 ER0 DR1 CL1 ER1 DL0 AR1 BR1,RWL 2 3)::
(makeTM BR1 HR1 CL1 ER0 DR1 CL1 ER1 DL0 AR1 CR0,RWL 3 3)::
(makeTM BR1 HR1 CL1 ER0 DR1 CL1 ER1 DL0 AR1 DR1,RWL 3 2)::
(makeTM BR1 HR1 CL1 ER0 DR1 DL0 EL1 AR0 CL0 CR1,RWL 4 2)::
(makeTM BR1 HR1 CL1 ER0 ER0 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 HR1 CL1 ER0 EL1 DL0 AR1 BL1 AL0 CR0,RWL 5 3)::
(makeTM BR1 HR1 CL1 ER0 EL1 DL0 BL0 AL1 DR0 DL1,RWL 4 2)::
(makeTM BR1 HR1 CL1 ER0 ER1 DL0 CR0 BL0 AL0 AR1,RWL 4 2)::
(makeTM BR1 HR1 CL1 EL1 DR0 CL0 BL0 AR1 ER0 BR0,RWL 2 3)::
(makeTM BR1 HR1 CL1 EL1 DR0 CL1 BL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 HR1 CL1 EL1 DR1 DL0 BL0 AR1 DL1 ER0,RWL 5 2)::
(makeTM BR1 HR1 CL1 EL1 ER1 DL1 BL0 AR0 DL0 CR0,RWL 5 2)::
(makeTM BR1 HR1 CL1 ER1 AL1 DL0 BL0 AR0 DL0 BR1,RWL 10 2)::
(makeTM BR1 HR1 CL1 ER1 AL1 DL0 BL1 BR0 DR0 EL1,RWL 3 2)::
(makeTM BR1 HR1 CL1 ER1 DL0 CL0 DR1 BR0 AR1 EL0,RWL 2 3)::
(makeTM BR1 HR1 CL1 ER1 DL0 CR0 AL1 BL1 CR1 BR0,RWL 15 2)::
(makeTM BR1 HR1 CL1 ER1 DL0 CL1 AR1 DL0 AR1 BR0,RWL 4 2)::
(makeTM BR1 HR1 CL1 ER1 DL0 CR1 BR1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 HR1 CL1 ER1 DL0 DR1 EL0 BR0 AR1 CR0,RWL 4 3)::
(makeTM BR1 HR1 CL1 ER1 DL0 DR1 EL0 BR0 AR1 EL0,RWL 2 4)::
(makeTM BR1 HR1 CL1 ER1 DL1 CL0 DR1 BR0 AR1 DL0,RWL 1 4)::
(makeTM BR1 HR1 CL1 ER1 DR1 BL0 AR0 CR1 ER0 DL0,RWL 7 2)::
(makeTM BR1 HR1 CL1 ER1 EL0 DL0 BL1 DR0 AR0 DL1,RWL 7 2)::
(makeTM BR1 HR1 CL1 ER1 ER0 DL0 AR1 BL1 AR1 CR0,RWL 24 2)::
(makeTM BR1 HR1 CR1 AR0 DL0 BR0 EL1 DR1 BR1 CL0,RWL 8 2)::
(makeTM BR1 HR1 CR1 AR0 DL1 BR0 EL0 CL0 AR1 EL0,RWL 2 3)::
(makeTM BR1 HR1 CR1 AR0 DL1 BR0 ER1 CL0 AR1 EL0,RWL 4 2)::
(makeTM BR1 HR1 CR1 AR0 DL1 DR1 BL0 EL0 BR1 CL0,RWL 3 2)::
(makeTM BR1 HR1 CR1 AR1 DL0 BR0 AL0 EL0 CL1 DL1,RWL 5 2)::
(makeTM BR1 HR1 CR1 AR1 DL1 EL0 ER1 CL0 DR0 AR0,RWL 2 2)::
(makeTM BR1 HR1 CR1 BL0 CL1 DR0 ER0 EL0 BL1 AR1,RWL 10 2)::
(makeTM BR1 HR1 CR1 BL0 DR0 CL1 BL1 ER1 AR0 DR1,RWL 11 2)::
(makeTM BR1 HR1 CR1 BL0 DL1 ER0 AR1 EL1 DR1 BL1,RWL 35 2)::
(makeTM BR1 HR1 CR1 BL0 DR1 ER0 EL0 DR0 AR0 BL1,RWL 4 2)::
(makeTM BR1 HR1 CR1 BR0 DL0 ER1 EL0 DL1 AR0 CR0,RWL 6 2)::
(makeTM BR1 HR1 CR1 BR0 DR0 BR1 DL1 EL0 BL0 AL1,RWL 2 4)::
(makeTM BR1 HR1 CR1 BR0 DR0 EL0 ER1 AR1 CL1 EL0,RWL 4 4)::
(makeTM BR1 HR1 CR1 BR0 DR0 ER0 DL1 EL0 BL0 AL1,RWL 2 4)::
(makeTM BR1 HR1 CR1 BR0 DL1 AR0 ER1 CL0 AR1 EL0,RWL 4 2)::
(makeTM BR1 HR1 CR1 BR0 DL1 EL0 EL1 DR1 AL1 CL1,RWL 4 3)::
(makeTM BR1 HR1 CR1 BR0 DL1 ER1 BL1 CL0 EL0 AR0,RWL 4 2)::
(makeTM BR1 HR1 CR1 BL1 BL0 DR1 AR1 ER0 BR0 CL0,RWL 11 3)::
(makeTM BR1 HR1 CR1 BL1 DL1 CL0 ER1 DR0 CL1 AR0,RWL 4 2)::
(makeTM BR1 HR1 CR1 BL1 DL1 DR0 AR1 EL0 AR0 BL0,RWL 3 3)::
(makeTM BR1 HR1 CR1 BL1 DL1 DR0 EL1 DR1 HR1 BL0,RWL 2 3)::
(makeTM BR1 HR1 CR1 BL1 DR1 DR0 EL1 DR1 HR1 BL0,RWL 2 3)::
(makeTM BR1 HR1 CR1 BR1 DL0 CL1 AR1 EL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 HR1 CR1 BR1 DL0 CL1 AR1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 HR1 CR1 BR1 DR0 EL0 ER1 AR1 CL1 DR0,RWL 2 3)::
(makeTM BR1 HR1 CR1 BR1 DL1 BR0 AL1 EL0 BL1 CL0,RWL 1 3)::
(makeTM BR1 HR1 CR1 BR1 DL1 DL0 ER1 CL0 AR0 DR1,RWL 4 3)::
(makeTM BR1 HR1 CR1 BR1 DR1 EL0 EL1 AR0 ER1 CL1,RWL 6 2)::
(makeTM BR1 HR1 CR1 BR1 DR1 EL0 ER1 AR1 CL1 DR0,RWL 4 4)::
(makeTM BR1 HR1 CR1 CL0 DL0 AR0 BL1 EL0 HR1 CL1,RWL 3 3)::
(makeTM BR1 HR1 CR1 CL0 DL0 AR0 BL1 EL0 DL0 EL1,RWL 3 2)::
(makeTM BR1 HR1 CR1 CL0 DR0 ER0 BL1 HR1 DL0 AR1,RWL 2 3)::
(makeTM BR1 HR1 CR1 CL0 DL1 AR0 BR1 EL0 AR1 BL0,RWL 4 3)::
(makeTM BR1 HR1 CR1 CL0 DL1 AR0 BR1 EL0 DR1 BL0,RWL 4 3)::
(makeTM BR1 HR1 CR1 CL0 DL1 BR0 BL0 ER0 AR1 DR1,RWL 4 2)::
(makeTM BR1 HR1 CR1 CL0 DL1 BR0 ER1 DL0 BL1 AR0,RWL 5 2)::
(makeTM BR1 HR1 CR1 CL0 DR1 AR0 EL0 BR0 BL1 DL1,RWL 9 2)::
(makeTM BR1 HR1 CR1 CL0 DR1 EL0 EL1 AR0 AR1 CL1,RWL 4 2)::
(makeTM BR1 HR1 CR1 CL0 DR1 EL0 ER1 BR0 CL1 AR0,RWL 8 2)::
(makeTM BR1 HR1 CR1 CR0 BL1 DR0 DL1 ER1 AR1 EL0,RWL 5 2)::
(makeTM BR1 HR1 CR1 CR0 DL0 BR0 ER1 DL1 AR1 EL0,RWL 9 2)::
(makeTM BR1 HR1 CR1 CR0 DL0 ER1 AR0 CL0 DL1 DR0,RWL 7 2)::
(makeTM BR1 HR1 CR1 CR0 DL1 EL0 AL1 BL1 BR0 EL1,RWL 1 3)::
(makeTM BR1 HR1 CR1 CR0 DL1 EL0 AL1 CL1 BR0 EL1,RWL 1 3)::
(makeTM BR1 HR1 CR1 CR0 DL1 EL0 ER1 BL1 CL0 AR0,RWL 3 3)::
(makeTM BR1 HR1 CR1 CR0 DL1 ER0 EL0 DL1 AR1 EL0,RWL 3 3)::
(makeTM BR1 HR1 CR1 CR0 DL1 ER1 BL0 EL0 AR0 DL0,RWL 4 3)::
(makeTM BR1 HR1 CR1 CL1 DR1 EL0 EL0 AR0 BL1 BL0,RWL 3 3)::
(makeTM BR1 HR1 CR1 DL0 BL1 BR0 EL1 BL1 AR0 EL0,RWL 2 3)::
(makeTM BR1 HR1 CR1 DL0 BL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 HR1 CR1 DL0 BL1 DR0 CR1 EL1 CL0 AL0,RWL 5 2)::
(makeTM BR1 HR1 CR1 DL0 BL1 ER0 CL0 DL1 BR0 AR1,RWL 3 2)::
(makeTM BR1 HR1 CR1 DL0 BL1 ER0 CL1 EL1 AL0 BR0,RWL 3 2)::
(makeTM BR1 HR1 CR1 DL0 DL0 AR1 BL1 ER0 DR1 BL1,RWL 2 3)::
(makeTM BR1 HR1 CR1 DL0 DL0 AR1 BL1 ER0 DR1 BR1,RWL 2 3)::
(makeTM BR1 HR1 CR1 DL0 DR0 ER0 EL1 CR0 BL0 AL0,RWL 8 2)::
(makeTM BR1 HR1 CR1 DL0 DL1 AR0 AR1 EL0 DR1 BL1,RWL 9 2)::
(makeTM BR1 HR1 CR1 DL0 DR1 AR0 EL1 BL1 ER1 DR1,RWL 4 2)::
(makeTM BR1 HR1 CR1 DL0 DR1 AR1 BL1 EL1 BL0 ER0,RWL 6 2)::
(makeTM BR1 HR1 CR1 DL0 DR1 EL0 BL1 CR0 AR1 ER1,RWL 6 2)::
(makeTM BR1 HR1 CR1 DL0 DR1 EL0 ER1 AR1 CL1 DR0,RWL 4 4)::
(makeTM BR1 HR1 CR1 DR0 BL1 AR0 ER1 EL0 DL1 CL0,RWL 6 3)::
(makeTM BR1 HR1 CR1 DR0 DL0 BR0 EL0 DR1 AL0 EL1,RWL 2 2)::
(makeTM BR1 HR1 CR1 DR0 DL0 CR0 AR0 EL0 CL0 EL1,RWL 7 2)::
(makeTM BR1 HR1 CR1 DR0 DL0 CR0 AR1 EL0 CL0 EL1,RWL 4 2)::
(makeTM BR1 HR1 CR1 DR0 DL1 BL0 ER1 DL1 AR1 EL0,RWL 2 4)::
(makeTM BR1 HR1 CR1 DR0 DL1 BR0 AL0 EL1 CL0 EL0,RWL 3 2)::
(makeTM BR1 HR1 CR1 DR0 DL1 BR0 ER1 CL0 AR1 EL0,RWL 4 2)::
(makeTM BR1 HR1 CR1 DR0 DL1 BR0 ER1 EL0 CL0 AR1,RWL 1 4)::
(makeTM BR1 HR1 CR1 DR0 DL1 BL1 ER1 CL0 BR1 AR0,RWL 4 3)::
(makeTM BR1 HR1 CR1 DR0 DL1 BL1 ER1 CL0 EL0 AR0,RWL 4 2)::
(makeTM BR1 HR1 CR1 DR0 DL1 CL1 ER1 CL0 HR1 BR0,RWL 1 3)::
(makeTM BR1 HR1 CR1 DL1 BL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 HR1 CR1 DR1 DL0 CR0 AR1 EL0 CL0 EL1,RWL 15 2)::
(makeTM BR1 HR1 CR1 DR1 DL0 EL1 AR1 EL0 CL1 BR0,RWL 4 2)::
(makeTM BR1 HR1 CR1 DR1 DL1 BR0 ER1 CL0 HR1 AR1,RWL 4 2)::
(makeTM BR1 HR1 CR1 DR1 DL1 ER1 EL0 BR0 AR0 CL0,RWL 3 3)::
(makeTM BR1 HR1 CR1 EL0 DL0 CL1 AR1 EL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 HR1 CR1 EL0 DR0 AR1 ER1 BR1 BL1 DR0,RWL 2 3)::
(makeTM BR1 HR1 CR1 EL0 DR0 BR0 ER1 AR0 BL1 CL0,RWL 2 3)::
(makeTM BR1 HR1 CR1 EL0 DR0 BR0 ER1 AR0 BL1 ER1,RWL 2 3)::
(makeTM BR1 HR1 CR1 EL0 DL1 AR1 ER1 BR1 BL1 DR0,RWL 2 3)::
(makeTM BR1 HR1 CR1 EL0 DL1 ER0 ER1 DL0 CL0 AR0,RWL 4 2)::
(makeTM BR1 HR1 CR1 EL0 DR1 AR0 BL1 BL1 DL0 BL1,RWL 35 2)::
(makeTM BR1 HR1 CR1 EL0 DR1 AR1 ER1 BR1 BL1 DR0,RWL 2 3)::
(makeTM BR1 HR1 CR1 EL0 DR1 BL1 ER1 AR0 BL0 CL1,RWL 3 2)::
(makeTM BR1 HR1 CR1 EL0 DR1 CL0 EL0 ER1 AR0 CL1,RWL 5 2)::
(makeTM BR1 HR1 CR1 EL0 DR1 CR0 BL1 AR0 DL0 BL0,RWL 4 2)::
(makeTM BR1 HR1 CR1 EL0 DR1 DL0 BL0 AR0 BL1 CL1,RWL 6 3)::
(makeTM BR1 HR1 CR1 ER0 CL0 DL1 AL1 DL1 CL1 BR0,RWL 2 3)::
(makeTM BR1 HR1 CR1 ER0 DL0 AR0 EL1 DR1 CR1 CL0,RWL 8 2)::
(makeTM BR1 HR1 CR1 ER0 DL0 AR1 EL1 BL1 CR0 EL0,RWL 3 2)::
(makeTM BR1 HR1 CR1 ER0 DL0 BR0 AL0 DL1 DL0 ER1,RWL 2 2)::
(makeTM BR1 HR1 CR1 EL1 DR0 CL1 BL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 HR1 CR1 EL1 DL1 BR0 CR1 BL0 CL0 AL0,RWL 5 2)::
(makeTM BR1 HR1 CR1 EL1 DR1 AR0 EL1 DR0 CL0 BL0,RWL 4 4)::
(makeTM BR1 HR1 CR1 ER1 DL0 CR1 BR1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 HR1 CR1 ER1 DR0 DL0 AL1 BL0 CL1 ER0,RWL 4 2)::
(makeTM BR1 HR1 CR1 ER1 DL1 AR1 EL1 DL0 BR0 CL0,RWL 4 3)::
(makeTM BR1 AL0 BL1 CL0 AL1 DL0 ER1 HR1 ER0 BR0,RWL 30 2)::
(makeTM BR1 AL0 BL1 CR0 DR1 DL0 AL1 ER0 AR0 HR1,RWL 6 2)::
(makeTM BR1 AL0 CL0 HR1 EL1 DR0 CR1 AR1 DL1 BL0,RWL 4 2)::
(makeTM BR1 AL0 CL0 CR0 DR1 AL1 AL1 ER0 AR0 HR1,RWL 6 2)::
(makeTM BR1 AL0 CL0 CR1 DR0 AL1 ER1 HR1 AR1 CL0,RWL 5 2)::
(makeTM BR1 AL0 CL0 DR0 AR0 AL1 ER1 HR1 AL1 CR0,RWL 3 3)::
(makeTM BR1 AL0 CL0 DR0 AL1 BR0 ER1 HR1 CR1 BL0,RWL 4 2)::
(makeTM BR1 AL0 CL0 DR0 BL1 AL1 ER1 HR1 CR0 ER1,RWL 15 2)::
(makeTM BR1 AL0 CL0 DL1 EL0 DR1 CR0 AR1 BL1 HR1,RWL 2 3)::
(makeTM BR1 AL0 CL0 ER0 HR1 DL1 AL1 AR0 BL1 DR0,RWL 4 3)::
(makeTM BR1 AL0 CL0 ER0 AL1 DR0 CL1 AR0 HR1 CR1,RWL 3 3)::
(makeTM BR1 AL0 CL0 ER0 DR1 DL0 AL1 DR0 CR0 HR1,RWL 4 2)::
(makeTM BR1 AL0 CR0 HR1 CL1 DL0 ER0 DL1 AL0 AR0,RWL 2 3)::
(makeTM BR1 AL0 CR0 HR1 CL1 DR1 ER1 AL1 AR1 DL1,RWL 6 2)::
(makeTM BR1 AL0 CR0 HR1 CL1 DR1 ER1 AL1 BR0 DL1,RWL 8 2)::
(makeTM BR1 AL0 CR0 HR1 DL0 AR0 EL1 DR0 AL0 DL1,RWL 4 2)::
(makeTM BR1 AL0 CR0 HR1 DL0 ER1 AL1 ER0 DR1 ER1,RWL 4 3)::
(makeTM BR1 AL0 CR0 HR1 DR0 DL1 ER0 AR0 EL1 AL0,RWL 12 2)::
(makeTM BR1 AL0 CR0 HR1 DL1 AR1 ER0 CL1 CR1 DR1,RWL 21 2)::
(makeTM BR1 AL0 CR0 HR1 DL1 CR1 AL1 EL0 DR1 ER0,RWL 11 2)::
(makeTM BR1 AL0 CR0 HR1 DL1 CR1 EL1 EL0 AR0 EL1,RWL 2 3)::
(makeTM BR1 AL0 CR0 HR1 DL1 CR1 ER1 EL0 AR0 EL1,RWL 2 3)::
(makeTM BR1 AL0 CR0 HR1 DL1 DR1 ER1 AL1 AR1 DL1,RWL 6 2)::
(makeTM BR1 AL0 CR0 HR1 DL1 ER1 AL1 ER0 DR1 EL1,RWL 5 4)::
(makeTM BR1 AL0 CR0 HR1 DR1 AL0 EL1 DR0 BL1 CL0,RWL 7 2)::
(makeTM BR1 AL0 CR0 HR1 DR1 AR0 EL1 EL0 AL0 DL1,RWL 2 2)::
(makeTM BR1 AL0 CR0 HR1 DR1 AR1 ER1 DL0 AL1 BR1,RWL 4 3)::
(makeTM BR1 AL0 CR0 HR1 DR1 AR1 ER1 DL0 AL1 CL0,RWL 4 3)::
(makeTM BR1 AL0 CR0 HR1 DR1 BR0 ER1 DL0 AL1 BR1,RWL 4 2)::
(makeTM BR1 AL0 CR0 HR1 DR1 CR0 ER1 DL0 AL1 BR1,RWL 4 2)::
(makeTM BR1 AL0 CR0 HR1 DR1 DL1 AL1 ER0 CR1 AR1,RWL 3 3)::
(makeTM BR1 AL0 CR0 HR1 DR1 DL1 AL1 ER0 ER0 AR1,RWL 3 3)::
(makeTM BR1 AL0 CR0 AL1 CL1 DR1 HR1 ER1 BR1 BL1,RWL 4 2)::
(makeTM BR1 AL0 CR0 AL1 DL1 ER0 BL1 HR1 CL0 BR1,RWL 9 2)::
(makeTM BR1 AL0 CR0 AL1 DR1 ER0 BL1 EL0 HR1 AR1,RWL 10 3)::
(makeTM BR1 AL0 CR0 AR1 DL1 CR1 EL0 AR0 HR1 AL1,RWL 16 2)::
(makeTM BR1 AL0 CR0 BR0 CL1 DL1 AR0 EL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 AL0 CR0 BR0 CL1 DL1 AR0 EL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL0 CR0 BR0 CL1 DR1 HR1 ER0 AL1 EL1,RWL 7 3)::
(makeTM BR1 AL0 CR0 BR0 DR0 HR1 DL1 EL1 AR1 BL1,RWL 3 2)::
(makeTM BR1 AL0 CR0 BR0 DR1 DL0 EL1 AR1 HR1 AL0,RWL 4 2)::
(makeTM BR1 AL0 CR0 BR0 DR1 DL1 AL1 ER0 HR1 CR0,RWL 2 3)::
(makeTM BR1 AL0 CR0 BL1 DL1 CR1 AL1 EL1 HR1 BL0,RWL 2 2)::
(makeTM BR1 AL0 CR0 BR1 DL1 CR1 EL0 ER0 HR1 AL1,RWL 8 2)::
(makeTM BR1 AL0 CR0 CL0 DL1 AR1 EL0 AR1 HR1 BL1,RWL 8 2)::
(makeTM BR1 AL0 CR0 CR1 DL0 ER1 AL1 AR0 DR1 HR1,RWL 38 2)::
(makeTM BR1 AL0 CR0 CR1 DR0 AR1 EL0 ER1 AL1 HR1,RWL 10 2)::
(makeTM BR1 AL0 CR0 CR1 DR1 HR1 EL0 ER0 AR1 AL1,RWL 10 2)::
(makeTM BR1 AL0 CR0 DR0 AL1 CL1 EL1 BR1 DL0 HR1,RWL 4 4)::
(makeTM BR1 AL0 CR0 DR0 AL1 EL0 CL1 BR1 DL1 HR1,RWL 4 4)::
(makeTM BR1 AL0 CR0 DR0 AL1 ER0 CL1 BR1 HR1 DL1,RWL 4 4)::
(makeTM BR1 AL0 CR0 DR0 CL1 AL1 HR1 ER1 AR1 CL1,RWL 15 2)::
(makeTM BR1 AL0 CR0 DR0 CL1 AL1 HR1 ER1 BR0 AR1,RWL 35 2)::
(makeTM BR1 AL0 CR0 DL1 DR1 AR1 BL1 EL1 HR1 BR0,RWL 3 2)::
(makeTM BR1 AL0 CR0 DL1 DR1 AR1 BL1 EL1 HR1 BL1,RWL 3 2)::
(makeTM BR1 AL0 CR0 DL1 DR1 DL1 AL1 ER1 HR1 BR0,RWL 7 2)::
(makeTM BR1 AL0 CR0 DR1 AL1 CL1 CL0 ER0 HR1 AR1,RWL 3 3)::
(makeTM BR1 AL0 CR0 DR1 CL1 AL1 HR1 ER0 AR1 ER1,RWL 30 2)::
(makeTM BR1 AL0 CR0 DR1 CL1 AL1 AL0 ER1 HR1 BR0,RWL 12 2)::
(makeTM BR1 AL0 CR0 DR1 DL1 AR1 EL0 CL0 HR1 AL1,RWL 8 2)::
(makeTM BR1 AL0 CR0 DR1 DL1 CR1 AL1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 AL0 CR0 DR1 DL1 ER1 AL1 DR0 HR1 DL0,RWL 24 2)::
(makeTM BR1 AL0 CR0 EL0 DL0 AR1 BL1 HR1 DL0 AL1,RWL 14 2)::
(makeTM BR1 AL0 CR0 ER0 CL1 DR1 BR1 AL1 HR1 AR0,RWL 16 2)::
(makeTM BR1 AL0 CR0 ER0 CL1 DR1 BR1 AL1 HR1 BR1,RWL 5 2)::
(makeTM BR1 AL0 CR0 ER0 DR0 HR1 AL1 EL0 EL1 AR1,RWL 3 3)::
(makeTM BR1 AL0 CR0 ER0 DL1 CR1 AL1 ER0 HR1 AR1,RWL 3 2)::
(makeTM BR1 AL0 CR0 ER0 DR1 HR1 ER0 DL0 EL1 AR1,RWL 3 3)::
(makeTM BR1 AL0 CR0 ER0 DR1 DL0 AL1 AR1 BR0 HR1,RWL 4 2)::
(makeTM BR1 AL0 CR0 ER0 DR1 DL0 AL1 AR1 CR0 HR1,RWL 4 2)::
(makeTM BR1 AL0 CR0 ER0 DR1 DL1 AL1 ER0 HR1 CR0,RWL 16 2)::
(makeTM BR1 AL0 CR0 EL1 DR1 HR1 BL1 ER0 BL0 AR1,RWL 5 3)::
(makeTM BR1 AL0 CR0 ER1 CL0 DR1 DL1 AL1 HR1 BR0,RWL 4 2)::
(makeTM BR1 AL0 CR0 ER1 CL1 DR0 HR1 AL1 BR1 DL1,RWL 4 2)::
(makeTM BR1 AL0 CR0 ER1 CL1 DR1 BR1 AL1 HR1 DR0,RWL 6 3)::
(makeTM BR1 AL0 CL1 HR1 DR0 CR1 ER0 AR1 EL1 AL0,RWL 9 3)::
(makeTM BR1 AL0 CL1 HR1 DR1 DL1 ER1 AL1 BR1 CR0,RWL 5 2)::
(makeTM BR1 AL0 CL1 AR0 HR1 DL1 EL1 EL0 ER1 BL0,RWL 6 2)::
(makeTM BR1 AL0 CL1 AR1 ER1 DL0 BL1 CR0 HR1 AR0,RWL 9 2)::
(makeTM BR1 AL0 CL1 BR0 DL0 BL0 AR0 EL1 AL1 HR1,RWL 6 2)::
(makeTM BR1 AL0 CL1 BR0 ER0 DL0 EL0 HR1 AL1 AR0,RWL 4 2)::
(makeTM BR1 AL0 CL1 BR0 ER1 DL0 CR0 DL1 HR1 AR1,RWL 7 2)::
(makeTM BR1 AL0 CL1 BL1 DR0 AL1 AR1 ER0 HR1 DR1,RWL 4 2)::
(makeTM BR1 AL0 CL1 BR1 DR1 CL0 ER0 HR1 AR1 CR1,RWL 2 4)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 AR1 ER0 HR1 BL0,RWL 15 2)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 AR1 ER0 HR1 BL1,RWL 15 2)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 AR1 ER0 HR1 DR1,RWL 4 3)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 AR1 ER1 HR1 BL0,RWL 4 3)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER1 CL1 BR0 HR1,RWL 8 2)::
(makeTM BR1 AL0 CL1 DR0 AL1 BL1 BL1 ER0 HR1 CR0,RWL 6 2)::
(makeTM BR1 AL0 CL1 DR0 AL1 BL1 BR1 ER0 HR1 CR0,RWL 7 2)::
(makeTM BR1 AL0 CL1 DR0 AR1 AL1 HR1 ER0 CL0 CR1,RWL 6 3)::
(makeTM BR1 AL0 CL1 DR0 AR1 AL1 HR1 ER0 EL1 CR1,RWL 15 2)::
(makeTM BR1 AL0 CL1 DR0 BR0 CR1 DL1 ER1 HR1 AL1,RWL 36 2)::
(makeTM BR1 AL0 CL1 DR0 EL1 AL1 CR0 DR1 BL0 HR1,RWL 8 3)::
(makeTM BR1 AL0 CL1 DR0 EL1 BR0 CL1 DR1 AL1 HR1,RWL 5 4)::
(makeTM BR1 AL0 CL1 DR0 ER1 DL1 CR1 AL1 AR1 HR1,RWL 35 2)::
(makeTM BR1 AL0 CL1 DR1 HR1 AL1 AR1 ER0 DR1 BL0,RWL 15 2)::
(makeTM BR1 AL0 CL1 DR1 AL0 DL0 ER1 BR1 BR0 HR1,RWL 2 3)::
(makeTM BR1 AL0 CL1 DR1 DR1 CL0 ER0 HR1 AR1 DR0,RWL 4 3)::
(makeTM BR1 AL0 CL1 DR1 DR1 CL0 ER0 HR1 AR1 ER0,RWL 4 3)::
(makeTM BR1 AL0 CL1 DR1 EL1 AL1 EL0 BR0 HR1 AR0,RWL 16 2)::
(makeTM BR1 AL0 CL1 EL0 DR0 DR1 BL1 CR1 HR1 AL1,RWL 13 2)::
(makeTM BR1 AL0 CL1 ER0 HR1 DL1 AL1 DR0 BL0 ER1,RWL 7 2)::
(makeTM BR1 AL0 CL1 ER0 AR0 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 AL0 CL1 ER0 AR0 DL0 DR1 BR0 HR1 CL1,RWL 2 2)::
(makeTM BR1 AL0 CL1 ER0 AL1 DR0 AR0 CL0 CR1 HR1,RWL 3 3)::
(makeTM BR1 AL0 CL1 ER0 AR1 DL1 BR1 CL1 HR1 CR0,RWL 7 3)::
(makeTM BR1 AL0 CL1 ER0 DL1 BL0 AL1 HR1 BR0 AL1,RWL 6 2)::
(makeTM BR1 AL0 CL1 ER1 AR0 DL0 DR1 BR0 HR1 CL1,RWL 2 2)::
(makeTM BR1 AL0 CL1 ER1 AR0 DL0 DR1 BR0 HR1 DL0,RWL 2 2)::
(makeTM BR1 AL0 CL1 ER1 AL1 DL0 AL1 ER0 CR1 HR1,RWL 24 2)::
(makeTM BR1 AL0 CL1 ER1 AR1 DL0 AR1 BR0 CR0 HR1,RWL 4 2)::
(makeTM BR1 AL0 CR1 HR1 DR0 CR1 ER0 AR1 EL1 AL0,RWL 9 3)::
(makeTM BR1 AL0 CR1 HR1 DR0 ER1 EL0 DR1 AL1 BR0,RWL 20 2)::
(makeTM BR1 AL0 CR1 HR1 DL1 AR1 EL0 DL0 ER1 CR0,RWL 2 2)::
(makeTM BR1 AL0 CR1 HR1 DL1 DR1 EL0 DL0 ER1 AR0,RWL 1 4)::
(makeTM BR1 AL0 CR1 HR1 DR1 BR0 EL1 CR0 AL0 DL0,RWL 2 3)::
(makeTM BR1 AL0 CR1 HR1 DR1 BR0 EL1 CR0 AR1 DL0,RWL 4 2)::
(makeTM BR1 AL0 CR1 HR1 DR1 DR0 EL0 CR0 AR1 EL1,RWL 9 2)::
(makeTM BR1 AL0 CR1 HR1 DR1 DR0 EL1 AR0 AL0 EL1,RWL 3 3)::
(makeTM BR1 AL0 CR1 HR1 DR1 EL0 EL0 BR0 AL1 CL1,RWL 8 2)::
(makeTM BR1 AL0 CR1 HR1 DR1 ER0 EL1 CR0 AR1 DL0,RWL 4 2)::
(makeTM BR1 AL0 CR1 AR0 DL1 BR0 HR1 EL1 DL0 AL1,RWL 8 3)::
(makeTM BR1 AL0 CR1 AR0 DL1 CR0 EL1 AL1 BL0 HR1,RWL 8 3)::
(makeTM BR1 AL0 CR1 AR0 DR1 BR0 EL1 HR1 AL0 EL1,RWL 3 3)::
(makeTM BR1 AL0 CR1 AL1 BL0 DR0 ER0 HR1 EL0 BR0,RWL 15 2)::
(makeTM BR1 AL0 CR1 AL1 DR0 BR1 ER1 HR1 BL0 CR0,RWL 10 2)::
(makeTM BR1 AL0 CR1 AL1 DR1 BL0 EL0 BR0 HR1 DL1,RWL 3 3)::
(makeTM BR1 AL0 CR1 AL1 DR1 BL0 EL1 BR0 HR1 DL0,RWL 3 3)::
(makeTM BR1 AL0 CR1 AR1 DR0 ER1 EL0 BR0 AL1 HR1,RWL 10 2)::
(makeTM BR1 AL0 CR1 AR1 DL1 HR1 EL0 DL0 ER1 BR0,RWL 2 3)::
(makeTM BR1 AL0 CR1 AR1 DL1 ER0 BL1 DL0 BR0 HR1,RWL 3 3)::
(makeTM BR1 AL0 CR1 BR0 DL0 EL0 HR1 CL1 AL1 AR1,RWL 8 2)::
(makeTM BR1 AL0 CR1 BR0 DL1 ER0 BL1 DL0 AR1 HR1,RWL 4 2)::
(makeTM BR1 AL0 CR1 BR0 DR1 EL1 EL1 ER0 HR1 AL1,RWL 16 3)::
(makeTM BR1 AL0 CR1 BL1 DL0 ER0 HR1 AL1 AR1 CR0,RWL 4 3)::
(makeTM BR1 AL0 CR1 BR1 DR0 HR1 EL1 ER1 AL1 CR0,RWL 10 2)::
(makeTM BR1 AL0 CR1 BR1 DL1 ER0 AR1 AL1 HR1 DR0,RWL 8 2)::
(makeTM BR1 AL0 CR1 CL0 DL1 AR0 AL1 EL0 HR1 CL1,RWL 2 3)::
(makeTM BR1 AL0 CR1 CL0 DL1 AR0 AL1 EL0 HR1 DL1,RWL 4 3)::
(makeTM BR1 AL0 CR1 CL0 DL1 AR0 AL1 EL1 HR1 BR0,RWL 4 3)::
(makeTM BR1 AL0 CR1 CL0 DL1 CR0 AL1 ER0 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL0 CR1 CL0 DL1 EL0 HR1 AL1 ER1 BR0,RWL 2 4)::
(makeTM BR1 AL0 CR1 CL0 DL1 ER1 HR1 AL1 BR0 BR0,RWL 15 2)::
(makeTM BR1 AL0 CR1 CL0 DL1 ER1 HR1 AL1 BR0 CL0,RWL 15 2)::
(makeTM BR1 AL0 CR1 CL0 DL1 ER1 HR1 AL1 CL1 BR0,RWL 15 2)::
(makeTM BR1 AL0 CR1 CR0 DL1 AR0 HR1 EL0 BL1 EL1,RWL 2 3)::
(makeTM BR1 AL0 CR1 CR0 DL1 DR1 AR1 EL1 HR1 AL1,RWL 15 2)::
(makeTM BR1 AL0 CR1 CR0 DL1 ER0 HR1 AL1 AR0 AR1,RWL 8 3)::
(makeTM BR1 AL0 CR1 CR0 DL1 ER0 HR1 AL1 BR0 AR1,RWL 4 2)::
(makeTM BR1 AL0 CR1 CR1 DR0 ER1 EL0 BR0 AL1 HR1,RWL 3 3)::
(makeTM BR1 AL0 CR1 DL0 DR1 AR0 ER1 BL1 DL1 HR1,RWL 24 2)::
(makeTM BR1 AL0 CR1 DR0 DL1 CR0 EL1 BR1 AL1 HR1,RWL 16 2)::
(makeTM BR1 AL0 CR1 DR0 DL1 ER0 AR1 AL1 HR1 BR0,RWL 16 3)::
(makeTM BR1 AL0 CR1 DL1 BL0 ER0 AR1 BL1 HR1 DR0,RWL 2 3)::
(makeTM BR1 AL0 CR1 DL1 DL0 ER1 HR1 AL1 BL1 ER0,RWL 2 4)::
(makeTM BR1 AL0 CR1 DL1 DR0 CR0 EL0 AR1 BL1 HR1,RWL 2 3)::
(makeTM BR1 AL0 CR1 DL1 DR1 AR0 BL1 EL1 HR1 BR0,RWL 6 2)::
(makeTM BR1 AL0 CR1 DL1 DR1 ER0 BL0 AL1 HR1 BR0,RWL 3 3)::
(makeTM BR1 AL0 CR1 EL0 DR0 DR1 BL1 CR1 HR1 AL1,RWL 13 2)::
(makeTM BR1 AL0 CR1 ER0 DL0 HR1 AR1 EL1 DR1 AL1,RWL 15 2)::
(makeTM BR1 AL0 CR1 ER0 DL1 AL1 AR1 CL1 HR1 DR1,RWL 15 2)::
(makeTM BR1 AL0 CR1 ER0 DL1 BR1 HR1 AL1 CL1 ER1,RWL 16 2)::
(makeTM BR1 AL0 CR1 ER0 DL1 DR0 HR1 AL1 AR1 BR1,RWL 34 2)::
(makeTM BR1 AL0 CR1 ER0 DL1 DR0 HR1 AL1 AR1 CR1,RWL 2 3)::
(makeTM BR1 AL0 CR1 ER0 DL1 DR0 HR1 AL1 CL1 ER1,RWL 16 2)::
(makeTM BR1 AL0 CR1 EL1 DR1 HR1 EL1 DR0 AL1 BL0,RWL 16 2)::
(makeTM BR1 AL0 CR1 ER1 DL0 DR0 BR0 BL0 AL1 HR1,RWL 6 2)::
(makeTM BR1 AL0 CR1 ER1 DR0 HR1 ER0 EL0 AL1 BR1,RWL 5 3)::
(makeTM BR1 AL0 CR1 ER1 DL1 HR1 AL1 DL0 AR0 ER0,RWL 28 2)::
(makeTM BR1 AL0 CR1 ER1 DL1 AR0 BL1 DL0 HR1 CL0,RWL 2 3)::
(makeTM BR1 AR0 BL1 CR1 ER0 DL0 CL1 DL1 HR1 AR1,RWL 5 2)::
(makeTM BR1 AR0 CL0 AR0 AL1 DL1 EL1 HR1 BL1 EL0,RWL 4 4)::
(makeTM BR1 AR0 CL0 AR0 DL1 BL1 AL1 EL1 AL0 HR1,RWL 4 3)::
(makeTM BR1 AR0 CL0 AR1 AL1 DL1 EL0 BL1 BL0 HR1,RWL 3 2)::
(makeTM BR1 AR0 CL0 AR1 DL0 CL1 AR1 EL0 HR1 AL0,RWL 15 2)::
(makeTM BR1 AR0 CL0 CR0 AL1 DL1 EL1 HR1 BL1 AR1,RWL 4 3)::
(makeTM BR1 AR0 CL0 CR0 DL0 CL1 AR1 EL1 HR1 AL0,RWL 7 2)::
(makeTM BR1 AR0 CL0 DR0 AR1 DL0 CL1 ER0 BL1 HR1,RWL 18 2)::
(makeTM BR1 AR0 CL0 DL1 CR1 AL1 HR1 EL1 BL0 AR1,RWL 3 3)::
(makeTM BR1 AR0 CL0 DL1 CR1 AL1 HR1 EL1 BL0 EL0,RWL 3 2)::
(makeTM BR1 AR0 CL0 DL1 DR1 AL1 ER0 BL1 HR1 AR1,RWL 8 2)::
(makeTM BR1 AR0 CL0 DR1 DL0 CL1 ER0 BR0 AR1 HR1,RWL 6 2)::
(makeTM BR1 AR0 CL0 DR1 DL0 CL1 ER0 DL0 AR1 HR1,RWL 6 2)::
(makeTM BR1 AR0 CL0 DR1 DL1 CL1 ER0 CL0 HR1 AR1,RWL 5 2)::
(makeTM BR1 AR0 CL0 EL0 AR1 DL1 BL1 HR1 DR0 CR0,RWL 3 3)::
(makeTM BR1 AR0 CL0 EL0 DR0 BL1 CL1 AR1 HR1 DL1,RWL 2 3)::
(makeTM BR1 AR0 CL0 EL0 DR0 CL1 AR1 BL1 HR1 DL0,RWL 2 3)::
(makeTM BR1 AR0 CL0 ER0 HR1 DR1 EL1 BL1 AR1 DL0,RWL 4 2)::
(makeTM BR1 AR0 CL0 ER0 EL1 DL1 BL1 HR1 AR1 CR0,RWL 6 2)::
(makeTM BR1 AR0 CL0 EL1 DL1 BL1 ER1 CL1 HR1 AR1,RWL 2 4)::
(makeTM BR1 AR0 CL0 EL1 EL1 DL1 BL0 HR1 AR1 CL1,RWL 8 3)::
(makeTM BR1 AR0 CL0 ER1 AR1 DL1 BL1 DL1 HR1 AL1,RWL 3 3)::
(makeTM BR1 AR0 CL0 ER1 DL0 BL1 DR1 AR1 HR1 CL1,RWL 6 3)::
(makeTM BR1 AR0 CR0 CL1 DL0 ER0 EL1 HR1 AR1 BL0,RWL 6 2)::
(makeTM BR1 AR0 CR0 DL0 CL1 BR0 EL1 AL1 AL0 HR1,RWL 6 2)::
(makeTM BR1 AR0 CR0 DL0 DR1 ER1 BL1 DL0 AR1 HR1,RWL 4 4)::
(makeTM BR1 AR0 CR0 DL1 AL1 ER0 HR1 AL0 EL1 BL0,RWL 3 2)::
(makeTM BR1 AR0 CR0 EL1 DL1 BR0 BL0 HR1 AL0 CL1,RWL 4 2)::
(makeTM BR1 AR0 CL1 HR1 DL0 CL0 DR1 EL1 AL0 AR1,RWL 2 3)::
(makeTM BR1 AR0 CL1 AL0 DR0 DL1 EL0 AR1 BL1 HR1,RWL 4 2)::
(makeTM BR1 AR0 CL1 AL0 DL1 BL0 ER1 DR1 HR1 AR1,RWL 10 3)::
(makeTM BR1 AR0 CL1 AL0 ER1 DL0 BL0 CR1 HR1 AR1,RWL 2 3)::
(makeTM BR1 AR0 CL1 AR0 AL1 DL0 EL1 HR1 CL0 BL0,RWL 4 2)::
(makeTM BR1 AR0 CL1 AR0 DL0 BL0 DR1 ER0 CR1 HR1,RWL 2 3)::
(makeTM BR1 AR0 CL1 AR0 DL1 BL0 EL0 BL1 AL1 HR1,RWL 2 3)::
(makeTM BR1 AR0 CL1 AR0 DR1 DL0 BL0 ER0 AR0 HR1,RWL 8 3)::
(makeTM BR1 AR0 CL1 AR0 DR1 DL0 BL0 ER1 AL1 HR1,RWL 8 3)::
(makeTM BR1 AR0 CL1 AR0 DR1 DL0 BL0 ER1 BL1 HR1,RWL 8 3)::
(makeTM BR1 AR0 CL1 AR1 EL1 DL0 BL1 AL0 AL1 HR1,RWL 6 2)::
(makeTM BR1 AR0 CL1 BL0 AR1 DL0 EL1 HR1 AL1 ER1,RWL 4 3)::
(makeTM BR1 AR0 CL1 BL0 DL1 CR1 AL0 EL1 HR1 AL1,RWL 10 2)::
(makeTM BR1 AR0 CL1 BR0 AL0 DL0 AL1 EL1 BL1 HR1,RWL 5 2)::
(makeTM BR1 AR0 CL1 BR0 EL0 DL0 BL1 HR1 ER1 AL1,RWL 2 3)::
(makeTM BR1 AR0 CL1 BR0 EL1 DL1 BL0 DL0 AR1 HR1,RWL 28 2)::
(makeTM BR1 AR0 CL1 BL1 DL0 BL0 ER1 AL1 DR1 HR1,RWL 4 3)::
(makeTM BR1 AR0 CL1 BL1 DL1 BL0 EL0 HR1 ER1 AL1,RWL 5 3)::
(makeTM BR1 AR0 CL1 BL1 DR1 BL0 HR1 ER1 AR1 CR0,RWL 3 3)::
(makeTM BR1 AR0 CL1 BL1 EL0 DL0 CL1 HR1 ER1 AL1,RWL 4 3)::
(makeTM BR1 AR0 CL1 BR1 DR1 DL0 BL0 ER0 AR1 HR1,RWL 36 2)::
(makeTM BR1 AR0 CL1 CR0 AR1 DL0 CL1 EL1 CL1 HR1,RWL 4 2)::
(makeTM BR1 AR0 CL1 CR1 AL1 DL0 EL0 AR1 BL0 HR1,RWL 2 3)::
(makeTM BR1 AR0 CL1 CR1 AL1 DL1 EL0 CL0 CL0 HR1,RWL 3 3)::
(makeTM BR1 AR0 CL1 CR1 AR1 DL0 BL0 EL1 HR1 CR0,RWL 24 2)::
(makeTM BR1 AR0 CL1 DL0 DL1 BL0 ER1 DL1 HR1 AR1,RWL 4 3)::
(makeTM BR1 AR0 CL1 DL0 DL1 CR1 EL1 BL1 AR1 HR1,RWL 4 3)::
(makeTM BR1 AR0 CL1 DL0 EL1 AL1 HR1 BL1 AR1 CL1,RWL 5 2)::
(makeTM BR1 AR0 CL1 DL0 EL1 AL1 HR1 BL1 AR1 DR0,RWL 5 2)::
(makeTM BR1 AR0 CL1 DL0 EL1 AL1 AR1 CL1 DL1 HR1,RWL 5 2)::
(makeTM BR1 AR0 CL1 DR0 AL1 CL0 ER1 HR1 CR1 EL1,RWL 4 2)::
(makeTM BR1 AR0 CL1 DR0 DL0 BL0 AR1 EL0 AR0 HR1,RWL 4 2)::
(makeTM BR1 AR0 CL1 DR0 DL0 BL0 AR1 ER0 AL0 HR1,RWL 4 2)::
(makeTM BR1 AR0 CL1 DR0 DL0 BL0 AR1 ER0 CR0 HR1,RWL 20 2)::
(makeTM BR1 AR0 CL1 DR0 DL0 BL0 AR1 ER1 CL1 HR1,RWL 4 2)::
(makeTM BR1 AR0 CL1 DR0 DL1 CL0 AR1 ER0 HR1 AL0,RWL 12 2)::
(makeTM BR1 AR0 CL1 DL1 BR1 BL1 HR1 EL0 ER1 AL0,RWL 5 2)::
(makeTM BR1 AR0 CL1 DR1 AR1 DL1 CR1 ER0 HR1 BL0,RWL 6 2)::
(makeTM BR1 AR0 CL1 EL0 AR1 DL0 EL0 HR1 BL1 BR0,RWL 2 3)::
(makeTM BR1 AR0 CL1 EL0 DL0 BL1 DR1 AL0 HR1 BR0,RWL 5 2)::
(makeTM BR1 AR0 CL1 ER0 HR1 DL0 EL1 BL1 AR1 DL0,RWL 4 2)::
(makeTM BR1 AR0 CL1 ER0 AR1 DL0 BL0 HR1 BL1 DL1,RWL 28 2)::
(makeTM BR1 AR0 CL1 ER0 DR0 BL1 AL0 DR1 HR1 DL0,RWL 3 3)::
(makeTM BR1 AR0 CL1 ER0 DL1 CL0 AR1 DR1 CR1 HR1,RWL 2 4)::
(makeTM BR1 AR0 CL1 EL1 AR1 DL0 BL0 HR1 BL1 ER0,RWL 3 3)::
(makeTM BR1 AR0 CL1 EL1 AR1 DL0 BL1 DR0 HR1 CR0,RWL 2 3)::
(makeTM BR1 AR0 CL1 EL1 DL0 BL1 DR1 AL0 HR1 DL0,RWL 5 2)::
(makeTM BR1 AR0 CL1 EL1 DL1 BL1 DR1 AL0 HR1 DL0,RWL 5 2)::
(makeTM BR1 AR0 CL1 EL1 ER1 DL1 BL0 HR1 AL0 CR0,RWL 5 2)::
(makeTM BR1 AR0 CL1 ER1 AR1 DL0 BL0 HR1 BL1 EL1,RWL 6 2)::
(makeTM BR1 AR0 CR1 BL0 CL1 DR1 HR1 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 AR0 CR1 BL0 DR0 ER0 DL1 AL0 HR1 BL0,RWL 3 2)::
(makeTM BR1 AR0 CR1 BL0 DR0 ER1 DL1 AL0 HR1 DR0,RWL 3 2)::
(makeTM BR1 AR0 CR1 BL1 DR0 ER1 AL1 DL0 HR1 DR1,RWL 10 2)::
(makeTM BR1 AR0 CR1 BL1 DL1 CR0 EL0 CL0 AL1 HR1,RWL 2 4)::
(makeTM BR1 AR0 CR1 BL1 DL1 CR0 EL0 DL1 AL1 HR1,RWL 2 4)::
(makeTM BR1 AR0 CR1 BL1 DL1 DR1 AR0 EL0 HR1 CL0,RWL 2 3)::
(makeTM BR1 AR0 CR1 BR1 DL0 ER0 AL0 DL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR0 CR1 CR0 DL1 ER1 AR1 CL0 DR0 HR1,RWL 4 2)::
(makeTM BR1 AR0 CR1 DL0 BL0 AR1 HR1 EL1 AL0 EL1,RWL 12 2)::
(makeTM BR1 AR0 CR1 DL0 BL0 ER0 HR1 BL1 EL1 AL0,RWL 2 3)::
(makeTM BR1 AR0 CR1 DL0 DL1 DR0 HR1 EL1 ER0 AL0,RWL 2 3)::
(makeTM BR1 AR0 CR1 EL0 DR0 ER0 DL1 AL0 HR1 BL0,RWL 3 2)::
(makeTM BR1 AR0 CR1 EL0 DL1 AR1 HR1 CL0 AL0 EL1,RWL 18 2)::
(makeTM BR1 AR0 CR1 EL0 DL1 CL1 AR1 CL0 HR1 BL1,RWL 8 3)::
(makeTM BR1 AR0 CR1 EL0 DL1 DR0 HR1 EL1 ER0 AL0,RWL 2 3)::
(makeTM BR1 AR0 CR1 EL0 DL1 ER0 HR1 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AR0 CR1 EL0 DR1 AR1 BL0 AL0 HR1 DL1,RWL 8 2)::
(makeTM BR1 AR0 CR1 EL1 DL1 DR0 HR1 AL0 BL0 BR0,RWL 2 3)::
(makeTM BR1 AL1 AL0 CL0 DR1 CR1 BR0 ER0 HR1 BR0,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 AR1 DR1 EL1 AL0 HR1 DL1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DR0 ER0 DL1 AL0 HR1 DR1,RWL 2 4)::
(makeTM BR1 AL1 AL0 CR0 DL1 CR1 AL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 CR1 AL1 EL0 HR1 BR0,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 CR1 AL1 EL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 CR1 AR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 CR1 AR1 EL0 HR1 BR0,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 CR1 AR1 EL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 CR1 EL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 CR1 ER1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 ER1 AL1 AL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL1 ER1 AR1 AL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR1 AL1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 AL1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 AL1 DR0 EL0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 AL1 DR0 EL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 AL1 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL0 CR1 AR1 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL0 CR1 BR0 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 BR0 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 BR0 DR0 EL0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 BR0 DR0 EL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 BR0 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL0 CR1 BR0 DR1 DL1 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 AL0 CR1 BR1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 BR1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 BR1 DR0 EL0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 BR1 DR0 EL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 BR1 DL1 ER1 CL0 HR1 DR1,RWL 6 2)::
(makeTM BR1 AL1 AL0 CR1 BR1 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL0 CR1 BR1 DR1 AR0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 CL1 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL0 CR1 DR0 ER0 AL0 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DR0 ER0 AL0 DR1 HR1 DR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DR0 ER1 AL0 DR1 HR1 BL0,RWL 3 2)::
(makeTM BR1 AL1 AL0 CR1 DR0 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 AL0 CR1 DL1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DL1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DL1 DR0 EL0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DL1 DR0 EL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DL1 ER0 HR1 AL1 DL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DL1 ER0 AL0 DR1 HR1 DR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DL1 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 AL0 CR1 DR1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DR1 DR0 EL0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DR1 DR0 EL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DR1 ER0 AL0 BL0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DR1 ER0 AL0 DR1 HR1 DR1,RWL 2 2)::
(makeTM BR1 AL1 AL0 CR1 DR1 ER0 AR1 HR1 AR0 BL0,RWL 25 2)::
(makeTM BR1 AL1 AL0 CR1 DR1 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 AL1 CL0 DR0 CL1 ER1 DR1 HR1 BR1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CL0 DR0 CR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 AL1 CL0 DR1 CR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR0 HR1 DL0 ER0 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 HR1 DL1 DR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR0 HR1 DL1 ER0 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 HR1 DR1 EL1 CR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 HR1 DR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DL0 CR1 HR1 ER1 EL1 AL0,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DL0 CR1 EL1 DR0 AL0 HR1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DL0 CR1 ER1 DL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DR0 CL1 HR1 ER0 EL1 AL0,RWL 1 4)::
(makeTM BR1 AL1 AL1 CR0 DL1 CR1 HR1 AL0 HR1 HR1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DL1 CR1 HR1 EL0 BR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DL1 CR1 HR1 EL0 BR1 EL1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DL1 CR1 HR1 EL0 ER1 AL1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DL1 CR1 HR1 ER0 AL0 EL1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 DR1 CL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR0 ER0 DR0 DL1 AL0 HR1 BR0,RWL 2 4)::
(makeTM BR1 AL1 AL1 CR0 EL1 DR1 BL0 CR1 AL0 HR1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR0 EL1 DR1 DL0 CR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 AL1 CL1 HR1 DR0 EL1 DR1 AL0 CL0,RWL 2 2)::
(makeTM BR1 AL1 AL1 CL1 DL0 BR0 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 AL1 AL1 CL1 DL0 CL0 DR1 ER1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CL1 DR0 CL0 DR1 ER1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DL0 ER0 DL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DL0 ER0 DR1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 AL0 DR1 HR1 HR1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 AL0 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 BL1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 DL1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 EL0 DR1 BR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 EL0 DR1 BR1 CL0,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 EL0 DR1 BR1 EL1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 EL1 DR1 DL1 AL0,RWL 3 3)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 EL1 DR1 DR1 AL0,RWL 3 3)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR0 ER1 DR1 EL0 AL0,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DL1 EL0 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DL1 ER0 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 AL0 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 AR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 BR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 CL1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 EL0 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 EL0 DR0 EL1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 EL0 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 ER0 CL0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL1 CR1 HR1 DR1 ER0 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 AL1 CR1 CL1 DL0 HR1 EL0 ER1 BR0,RWL 3 2)::
(makeTM BR1 AL1 AL1 CR1 DL0 CR0 DL1 ER1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 AL1 CR1 DL1 CR0 EL0 HR1 EL1 BR1,RWL 2 3)::
(makeTM BR1 AL1 AL1 CR1 EL0 DR0 CR0 DR1 AL0 HR1,RWL 2 2)::
(makeTM BR1 AL1 BL0 CR0 DL1 CR1 CR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 BL0 CR0 DR1 DR0 EL1 AL0 HR1 CL1,RWL 2 4)::
(makeTM BR1 AL1 BL1 CR1 HR1 DR1 AL0 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 BL1 CR1 HR1 DR1 AL1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 BL1 CR1 HR1 DR1 EL0 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 BL1 CR1 HR1 DR1 EL1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 BL1 CR1 HR1 DR1 ER1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 BL1 CR1 ER1 DR0 DL1 AL0 HR1 CR0,RWL 1 3)::
(makeTM BR1 AL1 CL0 BL0 CR1 DR0 BL1 ER1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 CL0 BL0 CR1 DR1 AL1 ER1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 BL0 CR1 DR1 AL1 ER1 HR1 BL1,RWL 2 2)::
(makeTM BR1 AL1 CL0 BL0 CR1 DR1 AL1 ER1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 CL0 BR0 CL1 DR1 AL1 ER1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AL1 CL0 BR1 DR1 CL1 HR1 ER1 AL0 BR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 CR1 HR1 DR1 CL1 ER0 EL1 AL0,RWL 1 3)::
(makeTM BR1 AL1 CL0 CR1 EL1 DR1 AL1 BR0 HR1 AL0,RWL 3 4)::
(makeTM BR1 AL1 CL0 DR0 HR1 AL1 EL1 DR1 AL1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CL0 DR0 HR1 AL1 EL1 DR1 AR1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CL0 DR0 HR1 AL1 EL1 DR1 CL1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CL0 DR0 HR1 AL1 EL1 DR1 CR1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CL0 DR0 AL1 CR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CL0 DR1 HR1 AL1 AL1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 HR1 AL1 BR1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 HR1 AL1 CL1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 HR1 AL1 EL1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 HR1 AL1 ER1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 AL1 ER0 HR1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 AL1 ER1 HR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 AR1 ER1 HR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 BR1 ER0 HR1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 BR1 ER1 HR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 CR0 ER0 HR1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 CR0 ER0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 CR0 ER1 HR1 BL0,RWL 3 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 CR0 ER1 HR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 CL1 ER0 HR1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 CL1 ER1 HR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 CR1 ER0 HR1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 CR1 ER1 HR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 DL1 ER1 HR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL0 DR1 AL0 CR1 EL1 ER0 HR1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL1 CL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AL1 CR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 DR1 AR1 CL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER0 HR1 DL1 AL1 CL1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER0 HR1 DL1 AR1 CL1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER0 HR1 DL1 ER1 CL1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL0 EL1 CR1 DR1 AL1 DR0 HR1 BL0,RWL 6 2)::
(makeTM BR1 AL1 CL0 ER1 HR1 DR1 AL0 BL0 DR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 HR1 DR1 AL0 DR1 AL1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 HR1 DR1 AL0 DR1 BR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 HR1 DR1 AL0 DR1 CL1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 HR1 DR1 AL0 DR1 DR0 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 HR1 DR1 AL0 DR1 DL1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 HR1 DR1 AL0 DR1 DR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 DL0 CR1 HR1 AL1 AL1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 DL0 CR1 HR1 AL1 BR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 DL0 CR1 HR1 AL1 CL1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 DL0 CR1 HR1 AL1 CR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 DL0 CR1 HR1 AL1 DL1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 DL1 CR1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 DR1 CL1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CL0 ER1 DR1 CR1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CR0 BL0 DR1 BR1 ER1 HR1 AL1 CL0,RWL 5 2)::
(makeTM BR1 AL1 CR0 BL0 DR1 BR1 ER1 HR1 AL1 CR0,RWL 5 2)::
(makeTM BR1 AL1 CR0 BL1 CL1 DL1 ER0 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 BL1 DL1 CR1 AL0 EL1 HR1 BL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR0 DL1 CR1 AL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR0 DL1 CR1 AR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR0 DL1 CR1 EL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR0 DL1 CR1 ER1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR0 DL1 ER1 AL1 AL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR0 DL1 ER1 AR1 AL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 CL1 CL1 DL1 ER0 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 CL1 DL1 AL0 EL0 BL1 HR1 CR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 CL1 DL1 AL0 EL1 HR1 HR1 BL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 CL1 DL1 DR1 AR1 EL0 HR1 DL0,RWL 2 4)::
(makeTM BR1 AL1 CR0 CL1 DL1 DR1 BL1 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 CL1 DL1 ER1 CL0 HR1 AR1 EL0,RWL 2 4)::
(makeTM BR1 AL1 CR0 CR1 AL1 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR0 CR1 CL1 DL1 ER0 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR1 DL0 ER0 AL1 HR1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR0 CR1 DL0 ER0 EL1 HR1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR0 CR1 DL0 ER0 ER1 HR1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR0 CR1 DL1 AR0 AR0 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR1 DL1 AR0 BL1 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR1 DL1 AR0 BR1 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR1 DL1 AR0 EL1 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 CR1 DL1 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 CR0 CR1 DR1 ER1 AL0 BL0 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 CR0 CR1 DR1 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 CR0 DL0 CL1 AL0 ER0 DR0 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DL0 CL1 AL0 ER0 DR0 HR1 BL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 DL0 CL1 AL0 ER1 DR0 HR1 CR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DL0 DL1 AL0 EL1 BR0 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 AL1 HR1 EL1 DR1 DL1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 AL1 HR1 EL1 DR1 DR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 HR1 EL0 EL0 AR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 HR1 EL1 EL0 BR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 HR1 ER1 BR0 CL1,RWL 1 4)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 HR1 ER1 CL1 DR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 HR1 ER1 CL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 EL0 DL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 EL0 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 EL0 DR1 HR1 CR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 ER0 CR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 ER0 CR1 HR1 BL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 ER1 CR1 HR1 CR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 AL0 ER1 CR1 HR1 CR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 DL1 AL0 AL0 ER0 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 DL1 AL0 AL0 ER0 HR1 BL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 DL1 AL0 AL0 ER1 HR1 BL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 DL1 AL0 AL0 ER1 HR1 CR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 DL1 AL0 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR0 DL1 CR1 AL0 ER1 HR1 AL0,RWL 3 2)::
(makeTM BR1 AL1 CR0 DR0 DL1 CR1 ER0 AL0 HR1 CL1,RWL 1 3)::
(makeTM BR1 AL1 CR0 DL1 CL1 BR0 AL0 EL1 AL0 HR1,RWL 4 2)::
(makeTM BR1 AL1 CR0 DL1 CL1 BR0 DR0 EL1 AL0 HR1,RWL 4 2)::
(makeTM BR1 AL1 CR0 DL1 DL1 AL0 EL1 AL0 HR1 BL1,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR1 CL1 AL0 HR1 ER0 AL0 CR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR1 CL1 AL0 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR0 DR1 CL1 AL0 HR1 ER0 BR0 AL0,RWL 1 4)::
(makeTM BR1 AL1 CR0 DR1 CL1 AL0 HR1 ER0 BL1 CR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR1 CL1 AL0 HR1 ER0 EL1 CR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 DR1 CL1 AL0 ER0 DL0 AR0 HR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 EL0 DR1 HR1 EL1 DR0 AR1 BL0,RWL 9 2)::
(makeTM BR1 AL1 CR0 ER0 DL0 HR1 EL1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DL0 HR1 ER1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DL0 AL0 AL1 HR1 CL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DR0 HR1 EL1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DR0 AL0 CL1 DL1 HR1 CR0,RWL 3 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 HR1 AL1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 HR1 AR1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 AL0 CL1 HR1 CL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 AL0 CL1 AL1 HR1 CR0,RWL 3 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 AL0 CL1 AR1 HR1 CR0,RWL 3 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 AL0 CL1 DR1 HR1 DR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 AL0 CL1 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 AL0 CR1 HR1 CL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER0 DL1 AL0 EL0 HR1 CL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR0 EL1 CL1 DL1 ER0 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 EL1 DL1 AL0 DL1 BL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR0 EL1 DL1 BR0 CL1 HR1 AL0 EL1,RWL 4 2)::
(makeTM BR1 AL1 CR0 EL1 DL1 ER1 CL0 HR1 AR1 EL0,RWL 2 2)::
(makeTM BR1 AL1 CR0 EL1 DR1 ER1 BL1 HR1 AR1 EL0,RWL 2 4)::
(makeTM BR1 AL1 CR0 ER1 DR0 CL1 DL1 AL0 HR1 CL0,RWL 1 4)::
(makeTM BR1 AL1 CR0 ER1 DL1 HR1 AL0 DR1 AL1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER1 DL1 HR1 AL0 DR1 AR1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER1 DL1 HR1 AL0 DR1 BL1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CR0 ER1 DL1 HR1 AL0 DR1 BR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CR0 ER1 DL1 HR1 AL0 DR1 DR0 BL0,RWL 2 2)::
(makeTM BR1 AL1 CR0 ER1 DL1 HR1 AL0 DR1 DR0 DR0,RWL 2 2)::
(makeTM BR1 AL1 CR0 ER1 DL1 HR1 AL0 DR1 DL1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER1 DL1 HR1 AL0 DR1 DR1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER1 DL1 AL0 CL1 CR0 HR1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR0 ER1 DL1 CL0 AR1 DR0 HR1 CR1,RWL 10 2)::
(makeTM BR1 AL1 CL1 AR0 HR1 DL0 EL0 DL1 AR1 BL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 AR0 DL0 BL0 DR1 ER0 CR1 HR1,RWL 2 3)::
(makeTM BR1 AL1 CL1 AR0 DR1 CL0 ER0 HR1 BL1 AR1,RWL 5 4)::
(makeTM BR1 AL1 CL1 BL0 DR1 CR0 BL1 ER0 AR1 HR1,RWL 4 2)::
(makeTM BR1 AL1 CL1 BR0 CR0 DL1 EL0 HR1 AL1 AR0,RWL 1 4)::
(makeTM BR1 AL1 CL1 BR0 DL0 AL1 DL1 ER1 HR1 BR1,RWL 2 3)::
(makeTM BR1 AL1 CL1 BR0 DL0 AR1 DL1 ER1 HR1 BR1,RWL 2 3)::
(makeTM BR1 AL1 CL1 BR0 DL0 AR1 DL1 ER1 HR1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 BR0 DL0 BL1 EL1 HR1 AL1 ER0,RWL 2 4)::
(makeTM BR1 AL1 CL1 BR0 DL0 BL1 EL1 HR1 AR1 ER0,RWL 2 4)::
(makeTM BR1 AL1 CL1 BR0 DL0 CL1 EL1 HR1 AL1 ER0,RWL 2 4)::
(makeTM BR1 AL1 CL1 BR0 DL0 CL1 EL1 HR1 AR1 ER0,RWL 2 4)::
(makeTM BR1 AL1 CL1 BR0 DL0 DL1 EL1 HR1 AL1 ER0,RWL 2 4)::
(makeTM BR1 AL1 CL1 BR0 DL0 DL1 EL1 HR1 AR1 ER0,RWL 2 4)::
(makeTM BR1 AL1 CL1 BR0 DL1 AR1 EL0 HR1 EL1 BR1,RWL 2 2)::
(makeTM BR1 AL1 CL1 BL1 ER1 DR0 HR1 BL0 AL0 CR0,RWL 5 2)::
(makeTM BR1 AL1 CL1 BR1 HR1 DL0 ER1 DL1 AR0 BR0,RWL 2 3)::
(makeTM BR1 AL1 CL1 BR1 HR1 DL1 AR0 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR0 HR1 DL1 ER0 EL1 CL1 AR1,RWL 1 4)::
(makeTM BR1 AL1 CL1 CR0 AL0 DR1 HR1 ER0 CL1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 CR0 AR0 DL0 EL1 HR1 AL1 EL0,RWL 36 2)::
(makeTM BR1 AL1 CL1 CR0 AR0 DL0 EL1 HR1 CL1 BL0,RWL 8 2)::
(makeTM BR1 AL1 CL1 CR0 AR1 DR1 EL1 AL0 HR1 DL1,RWL 2 3)::
(makeTM BR1 AL1 CL1 CR0 DL0 CR1 AR1 EL1 HR1 AL0,RWL 6 3)::
(makeTM BR1 AL1 CL1 CR0 DL1 CR1 HR1 EL1 AL1 AL0,RWL 3 3)::
(makeTM BR1 AL1 CL1 CR0 DL1 CR1 HR1 EL1 AR1 AL0,RWL 3 3)::
(makeTM BR1 AL1 CL1 CR0 DL1 CR1 CL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CL1 CR0 DL1 CR1 CR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CL1 CR0 DR1 CR1 EL0 AL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR0 DR1 DL0 AR1 EL0 HR1 AL0,RWL 3 2)::
(makeTM BR1 AL1 CL1 CL1 HR1 DL1 ER1 CL0 AR1 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 HR1 DR1 AR0 ER0 EL1 AL0,RWL 1 3)::
(makeTM BR1 AL1 CL1 CR1 HR1 DR1 CR0 ER0 EL1 AL0,RWL 1 4)::
(makeTM BR1 AL1 CL1 CR1 HR1 DR1 DR0 ER0 EL1 AL0,RWL 1 4)::
(makeTM BR1 AL1 CL1 CR1 HR1 DR1 ER0 CL0 EL1 AL0,RWL 1 3)::
(makeTM BR1 AL1 CL1 CR1 AL1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 AL1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 DL1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 DL1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 DR1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 ER0 DR0 AL0 DR1 DL1 HR1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 EL1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 EL1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 ER1 DR0 HR1 ER1 AL0 BL0,RWL 2 2)::
(makeTM BR1 AL1 CL1 CR1 ER1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DL0 AL0 CR1 ER1 DR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 HR1 AR0 DL1 EL0 BR1 BL1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 HR1 AR0 DL1 EL0 BR1 CL1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 HR1 AL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 HR1 AR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 HR1 DR1 BL0 ER0 EL1 AL0,RWL 1 3)::
(makeTM BR1 AL1 CL1 DR0 HR1 DR1 CR1 ER0 EL1 AL0,RWL 1 3)::
(makeTM BR1 AL1 CL1 DR0 AL0 AL1 EL0 DR1 HR1 BR0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 AL0 AR1 EL0 DR1 HR1 BR0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 AL0 CR1 HR1 EL1 ER1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 AL0 CR1 EL0 DR1 HR1 BR0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 AL0 CR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 AL0 CR1 ER1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 AR0 CL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 AR0 DL0 ER1 AL0 CR1 HR1,RWL 13 2)::
(makeTM BR1 AL1 CL1 DR0 AL1 BL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 AR1 BL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 AR1 DL0 ER1 AL0 CR0 HR1,RWL 7 2)::
(makeTM BR1 AL1 CL1 DR0 AR1 DL0 ER1 AL0 CR1 HR1,RWL 3 3)::
(makeTM BR1 AL1 CL1 DR0 BR1 AL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 BR1 CL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 CR1 AL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR0 CR1 BL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 DR0 BL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR0 EL0 AR1 AR0 BR0 CL0 HR1,RWL 6 2)::
(makeTM BR1 AL1 CL1 DL1 EL1 BR0 CR1 CR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 HR1 AL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 HR1 AR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 HR1 DL0 AR1 ER0 BL0 ER1,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 CR0 HR1 HR1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 EL0 CR0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER0 AL0 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER0 BL1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER0 EL1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER1 AL0 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER1 AR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER1 BR0 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER1 BR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER1 CL0 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER1 CR0 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER1 CR0 DL0,RWL 3 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 HR1 ER1 DL1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL1 DR1 AL0 CR1 ER0 EL0 HR1 BR0,RWL 2 3)::
(makeTM BR1 AL1 CL1 DR1 AR0 CL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 BR1 AL1 HR1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 BR1 CL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CL1 DR1 DR0 CR1 EL0 CR0 AL0 HR1,RWL 2 2)::
(makeTM BR1 AL1 CL1 EL0 AL0 DR1 HR1 BR0 CR0 ER1,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 HR1 DL0 AR0 AL0 BL1 AR1,RWL 3 2)::
(makeTM BR1 AL1 CL1 ER0 HR1 DL0 AL1 BL0 DR1 AR1,RWL 1 4)::
(makeTM BR1 AL1 CL1 ER0 HR1 DL1 AR0 BL0 AL0 ER1,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 HR1 DL1 AR0 CL1 AL0 ER1,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 HR1 DL1 BR1 BL0 AL0 ER1,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 HR1 DL1 BR1 CL1 AL0 ER1,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 HR1 DL1 ER0 BL0 AL0 ER1,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 HR1 DL1 ER0 CL1 AL0 ER1,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 HR1 DR1 DL1 AL0 DR0 CR0,RWL 2 4)::
(makeTM BR1 AL1 CL1 ER0 AL1 DL0 BL0 HR1 AR0 CR0,RWL 3 3)::
(makeTM BR1 AL1 CL1 ER0 DR0 BL0 HR1 AR1 BL1 DR1,RWL 4 2)::
(makeTM BR1 AL1 CL1 ER0 DL1 CR1 HR1 AL0 AL0 DR0,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 DL1 CR1 HR1 AL0 BL1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 DL1 CR1 HR1 AL0 EL1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CL1 ER0 DR1 BL0 HR1 AR1 BL1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CL1 ER0 DR1 BL1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER0 DR1 CR1 DL1 AL0 HR1 DR0,RWL 1 3)::
(makeTM BR1 AL1 CL1 EL1 DL1 CR1 AL0 EL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 HR1 DL0 AR1 CL1 AR1 AR0,RWL 4 2)::
(makeTM BR1 AL1 CL1 ER1 HR1 DL0 EL1 AL1 AR0 CL0,RWL 6 3)::
(makeTM BR1 AL1 CL1 ER1 HR1 DR0 AL0 DR1 AL1 CR1,RWL 3 2)::
(makeTM BR1 AL1 CL1 ER1 HR1 DR0 AL0 DR1 DL1 CR1,RWL 3 2)::
(makeTM BR1 AL1 CL1 ER1 HR1 DR0 AL0 DR1 DR1 CR1,RWL 3 2)::
(makeTM BR1 AL1 CL1 ER1 HR1 DL1 AL1 CL0 DL0 AR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 HR1 DR1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 AL0 DR1 AL0 DR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 BL1 DR1 AL0 DR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 CL1 DR1 AL0 DR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 DL0 CR1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 DL0 CR1 BR1 AL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 DR0 CL1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CL1 ER1 DL1 CR1 HR1 AL0 AL1 CR0,RWL 3 3)::
(makeTM BR1 AL1 CL1 ER1 DL1 CR1 HR1 AL0 AR1 CR0,RWL 3 3)::
(makeTM BR1 AL1 CL1 ER1 DR1 CR1 DL0 AL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 AR0 DL1 ER1 BR1 CL1 HR1 DL0,RWL 3 3)::
(makeTM BR1 AL1 CR1 BL0 DR1 HR1 ER0 AL1 CL1 BR1,RWL 2 4)::
(makeTM BR1 AL1 CR1 BL0 DR1 HR1 ER1 AR0 AL1 DL0,RWL 2 4)::
(makeTM BR1 AL1 CR1 BL0 DR1 HR1 ER1 ER0 AL0 DR0,RWL 9 2)::
(makeTM BR1 AL1 CR1 BL0 DR1 AR0 ER1 HR1 AL1 CL0,RWL 2 4)::
(makeTM BR1 AL1 CR1 BL0 DR1 AL1 ER0 HR1 BL1 BR1,RWL 2 4)::
(makeTM BR1 AL1 CR1 BL0 DR1 BR1 ER1 HR1 AL1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 BR1 DL0 AL0 AL0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 BR1 DL0 AL0 CR0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 BR1 DL0 CL1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 BR1 DL1 AL0 AL0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 BR1 DL1 AL0 CR0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 BR1 DL1 CL1 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AL1 CR1 CL0 DR0 ER0 EL1 HR1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR0 AL0 DL0 EL1 AR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR0 DL0 CR1 AR1 EL1 HR1 AL0,RWL 6 3)::
(makeTM BR1 AL1 CR1 CR0 DL0 DR0 EL1 BL1 AL0 HR1,RWL 2 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 CR1 HR1 EL1 AL1 AL0,RWL 3 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 CR1 HR1 EL1 AR1 AL0,RWL 3 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 CR1 CL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 CR1 CR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 CR1 EL0 AL0 HR1 BL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 CR1 EL1 AL0 HR1 BL0,RWL 4 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 DR0 EL1 AL0 HR1 BL0,RWL 4 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 ER0 BL0 AL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 CR0 DL1 ER1 BL0 AL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 AL1 CR1 CR0 DR1 CR1 EL0 AL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 AL1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 AL1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 AL1 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR1 CR1 DR0 ER0 EL1 HR1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 DL1 DR0 HR1 ER1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 DL1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 DL1 ER0 HR1 AL1 DL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 DL1 ER0 AL0 DR1 HR1 DR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 DL1 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 CR1 DR1 DR0 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 DR1 ER0 AL0 BL0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 DR1 ER0 AL0 DR1 HR1 DR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 CR1 DR1 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 DL0 AL0 CR0 HR1 EL1 AL0 BL0,RWL 6 2)::
(makeTM BR1 AL1 CR1 DL0 AL0 CR0 HR1 EL1 BL1 AL1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DL0 AL0 CR0 HR1 EL1 BL1 AR1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DL0 AL0 CR0 HR1 EL1 CR1 BL0,RWL 3 3)::
(makeTM BR1 AL1 CR1 DL0 AL0 CR1 ER1 DR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 DL0 AL0 ER0 BL1 DL0 CR0 HR1,RWL 28 3)::
(makeTM BR1 AL1 CR1 DL0 AL1 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DL0 DR0 BR0 ER1 BL1 AL0 HR1,RWL 44 2)::
(makeTM BR1 AL1 CR1 DL0 DR1 AR0 ER1 BL1 AL1 HR1,RWL 12 2)::
(makeTM BR1 AL1 CR1 DL0 DR1 BR0 EL1 CL0 HR1 AL0,RWL 4 4)::
(makeTM BR1 AL1 CR1 DR0 AL0 HR1 CL1 ER0 BR0 AL1,RWL 6 2)::
(makeTM BR1 AL1 CR1 DR0 AL0 HR1 ER0 DR1 CL1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 AL0 AL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 AL0 AR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 AL0 CR1 HR1 EL1 ER1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR0 AL0 CR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 AL0 CR1 ER1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR0 AL0 ER0 HR1 AL0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR0 AL0 ER0 HR1 BL1 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR0 AL1 HR1 EL1 DR1 AL1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 AL1 HR1 EL1 DR1 AR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 AL1 AL0 CL1 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 AL1 EL0 CL1 DR1 HR1 AL1,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 AL1 ER0 HR1 AL0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR0 BL0 HR1 EL1 DR1 AL1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 BL0 HR1 EL1 DR1 AR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 BL1 AL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 CL0 AL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 CL1 DL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 CL1 DL1 ER1 AL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 CL1 DR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DL0 HR1 EL1 DR1 DL1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DL0 HR1 EL1 DR1 DR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DR0 HR1 EL1 DR1 DL1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DR0 HR1 EL1 DR1 DR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DL1 DL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DL1 DR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DL1 EL1 AR0 CL0 BL0 HR1,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DR1 DL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR0 DR1 DR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DL1 AL0 ER0 HR1 AL0 EL1 BL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DL1 AL0 ER0 DR1 CL1 HR1 BR0,RWL 3 3)::
(makeTM BR1 AL1 CR1 DL1 AL0 ER0 ER0 CL1 HR1 BR0,RWL 3 3)::
(makeTM BR1 AL1 CR1 DL1 BL1 ER0 HR1 AL0 EL1 BL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 HR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 HR1 CL0 ER0 DR0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 BR1 HR1 EL0 CL1 DL1,RWL 6 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 CR0 HR1 HR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 EL0 CR0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER0 AL0 CR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER0 BL1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER0 EL1 CR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER1 AL0 CR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER1 AR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER1 BR1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER1 CL0 CR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER1 CR0 CR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER1 CR0 DL0,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 CR1 HR1 ER1 DL1 CR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 DL0 HR1 ER0 AL0 CR1,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR1 AL0 EL0 HR1 CR0 BR0 BR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 EL0 HR1 CR0 BR0 CR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR1 AL0 ER0 HR1 CL0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 ER0 HR1 CR0 BL0 BL1,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR1 AL0 ER0 HR1 CR1 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL0 ER1 HR1 CR0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 AL1 ER0 HR1 CL0 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 AL1 ER0 HR1 CR1 AL0 ER1,RWL 3 2)::
(makeTM BR1 AL1 CR1 DR1 BL1 ER1 HR1 CR0 AL0 DL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 DR1 BL1 ER1 HR1 CR0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 CL0 AL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 AL1 CR1 DR1 DR0 CR1 EL0 CR0 AL0 HR1,RWL 2 2)::
(makeTM BR1 AL1 CR1 EL0 DR0 CR0 DL1 AL0 HR1 BL0,RWL 6 3)::
(makeTM BR1 AL1 CR1 EL0 DL1 CR0 BL0 AL0 HR1 CL1,RWL 21 2)::
(makeTM BR1 AL1 CR1 EL0 DL1 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 EL0 DR1 ER1 AL0 DR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER0 DL0 HR1 AL1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL0 HR1 AR1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL0 HR1 BR0 AL1 CL1 DR0,RWL 6 2)::
(makeTM BR1 AL1 CR1 ER0 DL0 AL0 HR1 CL1 CL1 AR1,RWL 3 3)::
(makeTM BR1 AL1 CR1 ER0 DL0 DR0 AL0 DR1 HR1 AL0,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER0 DL0 DR0 AL0 DR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 AL1 CR1 ER0 DR0 HR1 AL1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 HR1 EL1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 HR1 ER1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 BL0 HR1 AL0 AL0 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 BR0 AL0 DL1 HR1 AL0,RWL 6 2)::
(makeTM BR1 AL1 CR1 ER0 DL1 CR0 AL0 BL1 HR1 CL0,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 CR1 HR1 AL0 AL0 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 CR1 HR1 AL0 BL1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 CR1 HR1 AL0 EL1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 DL0 HR1 AL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 DR0 AL0 DR1 HR1 AL0,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER0 DL1 EL1 HR1 AL0 AL0 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 EL1 HR1 AL0 BL1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 EL1 HR1 AL0 EL1 DR0,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DL1 EL1 HR1 CL1 ER0 AL0,RWL 1 4)::
(makeTM BR1 AL1 CR1 ER0 DR1 HR1 EL1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DR1 HR1 ER1 AL0 DL1 ER1,RWL 2 3)::
(makeTM BR1 AL1 CR1 ER0 DR1 CL1 AL1 AL0 HR1 DR0,RWL 1 4)::
(makeTM BR1 AL1 CR1 ER0 DR1 CR1 DL1 AL0 HR1 DR0,RWL 1 3)::
(makeTM BR1 AL1 CR1 ER0 DR1 DR0 AL0 DR1 HR1 AL0,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER0 DR1 EL1 DL1 AL0 HR1 DR0,RWL 1 3)::
(makeTM BR1 AL1 CR1 EL1 CL0 DR0 DL1 BL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 AL1 CR1 EL1 DL1 CR0 AR0 AL0 HR1 BL0,RWL 5 2)::
(makeTM BR1 AL1 CR1 EL1 DL1 CR1 AL0 EL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 EL1 DR1 DR0 AL0 BR1 HR1 BL0,RWL 2 2)::
(makeTM BR1 AL1 CR1 ER1 CL0 DL1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 ER1 CL0 DR1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 ER1 DL0 HR1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 ER1 DL0 CR1 BR1 AL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 ER1 DL0 DR0 AL0 DR1 HR1 CL0,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER1 DL0 DR0 AL0 DR1 HR1 CR1,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER1 DL1 HR1 EL1 DL0 AR1 BR0,RWL 4 3)::
(makeTM BR1 AL1 CR1 ER1 DL1 BR0 AL0 DL1 HR1 CR1,RWL 6 2)::
(makeTM BR1 AL1 CR1 ER1 DL1 CR1 HR1 AL0 AL1 CR0,RWL 3 3)::
(makeTM BR1 AL1 CR1 ER1 DL1 CR1 HR1 AL0 AR1 CR0,RWL 3 3)::
(makeTM BR1 AL1 CR1 ER1 DL1 DR0 AL0 DR1 HR1 CL0,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER1 DL1 DR0 AL0 DR1 HR1 CR1,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER1 DR1 CR1 DL0 AL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 AL1 CR1 ER1 DR1 DR0 AL0 DR1 HR1 CL0,RWL 3 2)::
(makeTM BR1 AL1 CR1 ER1 DR1 DR0 AL0 DR1 HR1 CR1,RWL 3 2)::
(makeTM BR1 AR1 BL0 CL0 DR1 CL1 AL1 ER1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 BL0 CL0 DR1 CL1 AR1 ER1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 BL0 CL0 DR1 CL1 CL1 ER1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 BL1 CL0 CR1 DL1 HR1 EL1 AL0 AR0,RWL 4 3)::
(makeTM BR1 AR1 BL1 CL0 CR1 DR1 BL1 ER1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 BL1 CL0 DR1 CL1 AL1 ER0 HR1 BR0,RWL 1 3)::
(makeTM BR1 AR1 BL1 CL0 DR1 CL1 AR1 ER0 HR1 BR0,RWL 1 3)::
(makeTM BR1 AR1 BL1 CL1 AR0 DL0 HR1 EL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 BL1 CL1 AR0 DL1 HR1 EL1 BR0 ER0,RWL 2 2)::
(makeTM BR1 AR1 BL1 CL1 AR0 DL1 HR1 ER1 BL0 ER0,RWL 2 2)::
(makeTM BR1 AR1 BL1 CL1 AR0 DL1 HR1 ER1 BR0 ER0,RWL 2 2)::
(makeTM BR1 AR1 BL1 CL1 AR1 DL1 HR1 ER0 BL0 ER0,RWL 3 2)::
(makeTM BR1 AR1 BL1 CL1 AR1 DL1 ER0 DR0 BR0 HR1,RWL 3 2)::
(makeTM BR1 AR1 BL1 CL1 DR0 EL0 AR0 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 BL1 CR1 EL0 DL0 HR1 CL1 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 BL1 CR1 EL1 DL1 HR1 CL0 AR0 EL1,RWL 4 2)::
(makeTM BR1 AR1 CL0 AR0 HR1 DL1 EL1 AL0 AR1 BL0,RWL 11 2)::
(makeTM BR1 AR1 CL0 AR0 HR1 DL1 EL1 AL0 DR1 BL0,RWL 4 2)::
(makeTM BR1 AR1 CL0 BR0 AL1 DL1 BL1 ER1 HR1 DR0,RWL 15 2)::
(makeTM BR1 AR1 CL0 BR0 CL1 DL1 AR1 EL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 DR1 DL0 AL1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 DR1 DL1 AR1 EL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 DR1 DL1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 DR1 DL1 AR1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 ER0 DL0 AL1 CL1 AR0 HR1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 ER1 DL0 AL1 CL1 AL1 HR1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 ER1 DL0 AL1 CL1 AR1 HR1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 ER1 DL0 CL0 CL1 AL1 HR1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 ER1 DL0 CL0 CL1 AR1 HR1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BL1 ER1 DL0 EL1 CL1 AR1 HR1,RWL 2 2)::
(makeTM BR1 AR1 CL0 BR1 DR1 CL1 HR1 ER1 AL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 CL0 CR1 DR1 BL1 ER1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 DL1 HR1 DR1 EL1 CR0 AL1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 DL1 HR1 DR1 EL1 CR0 AL1 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 DR1 HR1 DL1 EL0 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 DR1 AL1 CL1 HR1 EL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL0 HR1 DL1 AL1 CL1 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL0 HR1 DL1 AL1 CL1 AR1 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL0 HR1 DL1 BR1 CL1 AR1 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 ER0 HR1 DL0 AL1 DL1 BR1 CR0,RWL 3 2)::
(makeTM BR1 AR1 CL0 EL1 HR1 DL0 AL1 CL1 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL1 HR1 DL1 AR1 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL1 HR1 DL1 AR1 CL0 DL1 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL1 HR1 DL1 BR1 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL1 HR1 DL1 EL0 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL1 HR1 DL1 EL1 CL0 AR0 CR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL1 HR1 DL1 EL1 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 EL1 HR1 DL1 ER1 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL0 ER1 HR1 DL0 AL1 DL1 AL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 ER1 HR1 DL0 AL1 DL1 BR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 ER1 HR1 DL0 AL1 DL1 DL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 ER1 HR1 DL0 AL1 DL1 DR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 ER1 HR1 DR0 AL1 DL1 DL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL0 ER1 HR1 DL1 EL1 BL0 AR0 CR0,RWL 3 3)::
(makeTM BR1 AR1 CL0 ER1 HR1 DL1 EL1 BL0 AR0 DL1,RWL 35 2)::
(makeTM BR1 AR1 CL0 ER1 HR1 DL1 EL1 BL0 AR0 EL1,RWL 3 3)::
(makeTM BR1 AR1 CL0 ER1 HR1 DL1 ER1 BL0 AR0 EL1,RWL 3 3)::
(makeTM BR1 AR1 CL0 ER1 AR1 DR1 DL1 BL0 CR0 HR1,RWL 9 2)::
(makeTM BR1 AR1 CL0 ER1 CR1 DR0 BL1 AL1 HR1 AR0,RWL 2 3)::
(makeTM BR1 AR1 CR0 HR1 CL1 DL1 AR0 EL1 BR0 ER0,RWL 3 2)::
(makeTM BR1 AR1 CR0 HR1 DL1 CR1 DL0 EL0 ER1 AL0,RWL 4 2)::
(makeTM BR1 AR1 CR0 HR1 DR1 CL0 DL1 EL1 CL1 AR0,RWL 6 2)::
(makeTM BR1 AR1 CR0 AR0 DL1 EL0 CL0 HR1 ER1 AL0,RWL 6 2)::
(makeTM BR1 AR1 CR0 BR0 CL1 DL1 AR1 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 AR1 CR0 BR0 CL1 DL1 AR1 EL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 AR1 CR0 BR0 CL1 DL1 AR1 EL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CR0 BR0 CL1 DL1 DR1 EL0 HR1 AL1,RWL 1 3)::
(makeTM BR1 AR1 CR0 BR0 CL1 DL1 ER0 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 AR1 CR0 BL1 CL1 DL1 AR0 EL0 HR1 CL1,RWL 3 2)::
(makeTM BR1 AR1 CR0 BL1 CL1 DL1 AR0 EL1 HR1 CL0,RWL 3 2)::
(makeTM BR1 AR1 CR0 BL1 DL0 AR1 CR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CR0 BL1 DL0 EL1 EL1 HR1 AR0 CL0,RWL 2 2)::
(makeTM BR1 AR1 CR0 BL1 DL1 EL1 ER1 HR1 AR0 CL0,RWL 2 2)::
(makeTM BR1 AR1 CR0 CR1 DL1 EL0 CL0 HR1 AR1 AL0,RWL 3 2)::
(makeTM BR1 AR1 CR0 DL1 DL1 AR1 EL1 DL0 HR1 AL0,RWL 3 3)::
(makeTM BR1 AR1 CR0 DL1 DR1 BL0 BL1 EL1 HR1 AL0,RWL 1 4)::
(makeTM BR1 AR1 CR0 DR1 AL1 CL1 CL0 ER0 HR1 BR1,RWL 3 2)::
(makeTM BR1 AR1 CR0 DR1 AL1 CL1 CL0 ER1 HR1 BR0,RWL 3 2)::
(makeTM BR1 AR1 CR0 EL0 CL1 DL1 AL0 BL0 HR1 DR0,RWL 3 2)::
(makeTM BR1 AR1 CR0 EL0 CL1 DR1 HR1 BL0 ER1 AL0,RWL 4 2)::
(makeTM BR1 AR1 CR0 EL0 DR0 ER1 EL1 HR1 AL1 BL1,RWL 5 2)::
(makeTM BR1 AR1 CR0 ER0 CL1 DR1 AL1 DL0 BR1 HR1,RWL 4 3)::
(makeTM BR1 AR1 CL1 AR0 HR1 DL0 DR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AR1 CL1 AR0 HR1 DL0 EL1 BL1 AR1 CR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 AR0 HR1 DL1 EL1 BL0 AL1 EL0,RWL 3 3)::
(makeTM BR1 AR1 CL1 AR0 DL0 BL0 DR1 ER0 CR1 HR1,RWL 2 3)::
(makeTM BR1 AR1 CL1 AR0 DR1 CL0 ER0 HR1 BL0 AR1,RWL 4 3)::
(makeTM BR1 AR1 CL1 AR0 DR1 CL0 ER0 HR1 BL1 ER1,RWL 3 4)::
(makeTM BR1 AR1 CL1 AR0 DR1 DL0 CR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 AR1 CL1 AR0 EL1 DL0 BL0 BL1 BR0 HR1,RWL 3 4)::
(makeTM BR1 AR1 CL1 BL0 ER1 DL1 CL0 DR0 AR0 HR1,RWL 9 2)::
(makeTM BR1 AR1 CL1 BR0 AR1 DL0 EL1 AL0 CL0 HR1,RWL 4 3)::
(makeTM BR1 AR1 CL1 BR0 DL0 CL0 DR1 EL1 HR1 AL0,RWL 7 3)::
(makeTM BR1 AR1 CL1 BR0 DL1 BL0 EL1 CL1 AR1 HR1,RWL 6 3)::
(makeTM BR1 AR1 CL1 BL1 HR1 DL1 AR0 ER0 BL0 ER1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AL0 DL1 AR0 EL0 HR1 CL1,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 AL0 DL1 AR0 EL1 HR1 CL0,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 AR0 EL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 AL1 EL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 AL1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 BL0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 CR0 EL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 CR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 CL1 EL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 CL1 EL0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 CL1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 AR0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 AL1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 AL1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 BR0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 CL0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 CL0 EL0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 CL1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 CL1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DR1 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DR1 AL1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DR1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DR1 BL0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DR1 BL1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DR1 BR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DR1 CR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 AR1 DR1 CL1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DL0 AR0 EL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DL0 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DL0 AR1 EL1 HR1 BR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DL0 AR1 EL1 HR1 CL1,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DL1 AR0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DL1 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DL1 AR1 EL0 HR1 CL1,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DL1 AR1 EL1 HR1 CL0,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 DL1 DR1 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 DR1 DL1 AR1 EL1 HR1 CL0,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL0 CL1 EL0 HR1 AR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL1 AR0 CL0 HR1 AL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL1 AR0 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL1 AR0 CL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL1 AL1 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL1 BR0 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL1 CL1 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DR1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 EL1 DR0 HR1 CL1 AR1 DL0,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AR0 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AR0 CL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AR0 CL0 HR1 AR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AR0 CL0 HR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AR0 CL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AR0 CL0 HR1 CL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AL1 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AL1 CL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AL1 CL0 HR1 AR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AL1 CL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 AR1 EL0 HR1 CL1,RWL 3 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 BR0 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 BR0 CL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 BR0 CL0 HR1 AR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 CL1 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 CL1 CL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 CL1 CL0 HR1 AR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL1 ER0 CL0 HR1 AR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 BR1 HR1 DL0 ER1 DL1 AL0 BR0,RWL 2 3)::
(makeTM BR1 AR1 CL1 BR1 HR1 DL1 AR0 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 CL0 DR0 BL0 CR1 ER1 AL1 HR1,RWL 6 2)::
(makeTM BR1 AR1 CL1 CL0 DR1 BL0 ER0 CR1 AR1 HR1,RWL 4 3)::
(makeTM BR1 AR1 CL1 CL0 DR1 BL1 AR0 ER1 HR1 BR0,RWL 2 4)::
(makeTM BR1 AR1 CL1 CR0 HR1 DL0 EL0 AL0 ER1 AR0,RWL 2 3)::
(makeTM BR1 AR1 CL1 CR0 EL1 DL0 AL1 BL1 AR0 HR1,RWL 2 3)::
(makeTM BR1 AR1 CL1 CR1 EL1 DR1 HR1 BR0 AL1 EL1,RWL 3 2)::
(makeTM BR1 AR1 CL1 DL0 AR1 BL0 DR1 ER0 BR1 HR1,RWL 14 2)::
(makeTM BR1 AR1 CL1 DL0 AR1 BL1 HR1 EL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 HR1 AL1 ER1 EL1 DL1 CL0,RWL 1 3)::
(makeTM BR1 AR1 CL1 DR0 HR1 DL1 EL1 EL0 AR0 BL1,RWL 8 2)::
(makeTM BR1 AR1 CL1 DR0 HR1 DL1 ER1 EL0 AL1 BL1,RWL 2 3)::
(makeTM BR1 AR1 CL1 DR0 AR0 BL0 BL1 ER0 HR1 AL1,RWL 4 2)::
(makeTM BR1 AR1 CL1 DR0 AR0 BL0 BL1 ER1 HR1 DR0,RWL 4 2)::
(makeTM BR1 AR1 CL1 DR0 AR0 BL1 AR1 ER1 HR1 CL0,RWL 6 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 AR0 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 AL1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 AR1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 BL0 ER0 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 BL0 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 BR1 ER0 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 BR1 ER0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 BR1 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 CL0 ER0 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 CL0 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 CR1 ER0 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 CR1 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR0 AL1 DL0 EL1 AR0 BL0 HR1,RWL 2 3)::
(makeTM BR1 AR1 CL1 DR0 AR1 BL0 BL1 ER0 HR1 BL0,RWL 3 2)::
(makeTM BR1 AR1 CL1 DR0 AR1 BL1 AR1 ER1 HR1 CL0,RWL 6 2)::
(makeTM BR1 AR1 CL1 DR0 AR1 DL0 EL1 AR0 BL0 HR1,RWL 2 4)::
(makeTM BR1 AR1 CL1 DR0 DL1 BL1 AR0 ER0 HR1 BL0,RWL 4 4)::
(makeTM BR1 AR1 CL1 DL1 AL1 BR0 CL1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 AL1 CL1 AR0 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 AL1 CL1 AL1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 AL1 CL1 AR1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 AL1 CL1 BL0 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 AL1 CL1 BR1 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 AL1 CL1 CL0 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 AL1 CL1 CL1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 AL1 CL1 CR1 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DL1 BR0 CL1 AL1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 HR1 BR1 EL0 BR0 AL1 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 HR1 BR1 EL1 CR0 AL1 EL1,RWL 3 2)::
(makeTM BR1 AR1 CL1 DR1 HR1 DL0 EL1 CL1 AR0 EL1,RWL 4 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 AL0 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 AL1 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 BL0 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 BR0 ER0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 BR0 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 BR1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 BR1 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 CL0 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 CL0 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 CR1 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 CR1 ER1 HR1 DR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 BR1 CL1 HR1 EL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 DR1 DL1 BL1 AR0 EL0 HR1 BL0,RWL 10 3)::
(makeTM BR1 AR1 CL1 DR1 DL1 BL1 AR0 EL0 HR1 CL1,RWL 5 2)::
(makeTM BR1 AR1 CL1 DR1 ER1 DL1 AL1 CL0 BR0 HR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL0 EL0 BL0 ER1 AR0,RWL 1 4)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL1 AR0 BL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL1 AL1 CL1 AR1 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL1 BR1 BL0 AR0 EL1,RWL 2 3)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL1 BR1 CL1 AR0 EL1,RWL 2 3)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL1 BR1 CL1 AR1 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL1 EL0 BL0 AR0 EL1,RWL 2 3)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL1 EL0 CL1 AR0 EL1,RWL 2 3)::
(makeTM BR1 AR1 CL1 EL0 HR1 DL1 ER0 BL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL0 AR1 DL0 BL1 AL1 HR1 AR0,RWL 7 2)::
(makeTM BR1 AR1 CL1 EL0 DR0 BL0 AL1 DR1 HR1 AR0,RWL 5 2)::
(makeTM BR1 AR1 CL1 EL0 DR0 BL0 AR1 DR1 HR1 AR0,RWL 5 2)::
(makeTM BR1 AR1 CL1 EL0 DL1 BL0 AR1 DL1 HR1 AR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 EL0 DL1 BL1 AR0 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL0 DR1 BL0 AR1 DL1 HR1 AR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 EL0 DR1 BL1 AR0 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL0 DR1 BL1 BR0 AR0 HR1 DL0,RWL 4 2)::
(makeTM BR1 AR1 CL1 EL0 DR1 DL0 BL1 AL1 HR1 AR0,RWL 7 2)::
(makeTM BR1 AR1 CL1 ER0 HR1 DL0 AL1 AL0 DL0 CR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 ER0 HR1 DL0 ER1 AL0 AR0 BL0,RWL 6 4)::
(makeTM BR1 AR1 CL1 ER0 AR0 DL0 BL0 DL1 CR1 HR1,RWL 7 2)::
(makeTM BR1 AR1 CL1 ER0 DL0 DR1 AR0 BL1 HR1 CR1,RWL 6 2)::
(makeTM BR1 AR1 CL1 ER0 DL1 CL1 AL1 AR0 HR1 BR1,RWL 4 2)::
(makeTM BR1 AR1 CL1 ER0 DL1 CL1 AL1 AR0 HR1 CL0,RWL 4 2)::
(makeTM BR1 AR1 CL1 ER0 DL1 CL1 AL1 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER0 DL1 CL1 ER0 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER0 DR1 BL0 HR1 AL1 BL1 CR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 ER0 DR1 BL0 HR1 AR1 BL1 CR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 ER0 DR1 CL0 EL1 HR1 CR1 AL1,RWL 5 2)::
(makeTM BR1 AR1 CL1 ER0 DR1 DL1 AR1 DL0 HR1 CR0,RWL 8 3)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL0 AR0 CL1 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL0 AL1 CL1 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL1 AR0 CL0 AL0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL1 AR0 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL1 AR0 CL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL1 AL1 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL1 BR0 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL1 ER0 CL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 AR1 CL1 EL1 DR0 DL0 BL1 AR0 HR1 CL0,RWL 1 3)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL0 AL1 AL0 AL0 CR0,RWL 3 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL0 AL1 DL1 AL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL0 AL1 DL1 BR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL0 AL1 DL1 DL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL0 AL1 DL1 DR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL0 DR1 BR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL1 AL1 DL1 AL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL1 AL1 DL1 BR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL1 AL1 DL1 CL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL1 AL1 DL1 DL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DL1 AL1 DL1 DR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DR1 AL1 DL1 AL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DR1 AL1 DL1 BR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DR1 AL1 DL1 DL0 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 HR1 DR1 AL1 DL1 DR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 DL0 CL1 AR0 DL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 DL1 CL1 AL1 AR0 HR1 BR0,RWL 4 3)::
(makeTM BR1 AR1 CL1 ER1 DL1 CL1 AL1 AR0 HR1 DL0,RWL 4 2)::
(makeTM BR1 AR1 CL1 ER1 DL1 CL1 AL1 AR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 AR1 CL1 ER1 DR1 DL0 CR1 BR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CR1 HR1 DR1 EL0 ER1 AL0 CL1 DR0,RWL 6 2)::
(makeTM BR1 AR1 CR1 AL0 DL0 CL1 AR1 EL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AR1 CR1 AL0 DL0 CL1 AR1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CR1 AR0 DL1 AL0 AR0 EL0 HR1 CL0,RWL 6 2)::
(makeTM BR1 AR1 CR1 AR0 DL1 AL0 AL1 EL0 HR1 CL0,RWL 8 2)::
(makeTM BR1 AR1 CR1 AR0 DL1 AL0 AR1 EL0 HR1 CL0,RWL 7 2)::
(makeTM BR1 AR1 CR1 AR0 DL1 AL0 BR0 EL0 HR1 CL0,RWL 5 2)::
(makeTM BR1 AR1 CR1 AR0 DL1 AL0 BR1 EL0 HR1 CL0,RWL 7 2)::
(makeTM BR1 AR1 CR1 AL1 DL0 ER0 AL0 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR1 AR1 CR1 AR1 DL0 ER0 AL0 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR1 AR1 CR1 BL0 DR0 ER1 DL1 BL1 HR1 AR0,RWL 30 2)::
(makeTM BR1 AR1 CR1 BL1 CL1 DL1 HR1 EL1 AR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CR1 BL1 DL0 EL1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CR1 BL1 DL1 DR1 AR0 EL0 HR1 CL0,RWL 2 3)::
(makeTM BR1 AR1 CR1 BL1 DL1 EL1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CR1 CL0 DL1 CL1 AR0 EL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CR1 CR0 DL0 ER0 AL1 DL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 AR1 CR1 CR0 DL0 ER1 AL1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AR1 CR1 CR0 DL1 AL0 AR0 EL0 HR1 CL0,RWL 1 4)::
(makeTM BR1 AR1 CR1 CR0 DL1 ER1 AL1 DL1 HR1 AL0,RWL 3 2)::
(makeTM BR1 AR1 CR1 CR0 DL1 ER1 AL1 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 AR1 CR1 CL1 DL0 AR0 ER1 DL1 HR1 BR0,RWL 2 4)::
(makeTM BR1 AR1 CR1 CL1 DL0 ER1 AL1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AR1 CR1 CL1 DL1 CL1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 AR1 CR1 CL1 DL1 CL1 AR1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 AR1 CR1 CR1 DL0 ER0 AL1 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR1 AR1 CR1 CR1 DL0 ER1 AL1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 AR1 CR1 CR1 DL1 ER0 AL1 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 AR1 CR1 CR1 DL1 ER1 AL1 DL1 HR1 BR0,RWL 3 2)::
(makeTM BR1 AR1 CR1 DL0 DL1 ER0 DR1 BL1 AR1 HR1,RWL 6 2)::
(makeTM BR1 AR1 CR1 DL0 DR1 ER1 BL1 CR0 AR1 HR1,RWL 4 4)::
(makeTM BR1 AR1 CR1 DR0 DL1 AL0 HR1 EL0 AL0 BL1,RWL 3 2)::
(makeTM BR1 AR1 CR1 DR0 DL1 BR1 HR1 EL0 AL0 BL1,RWL 3 2)::
(makeTM BR1 AR1 CR1 DR1 DL1 BR0 ER1 CL0 HR1 AL1,RWL 4 2)::
(makeTM BR1 AR1 CR1 EL0 DL1 ER0 AL1 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 AR1 CR1 EL0 DR1 AR0 EL1 AL0 HR1 DL1,RWL 4 3)::
(makeTM BR1 AR1 CR1 ER0 DL0 HR1 AL1 DL1 CL1 BR1,RWL 4 2)::
(makeTM BR1 AR1 CR1 ER0 DL1 EL1 HR1 CL0 AR1 EL0,RWL 8 3)::
(makeTM BR1 AR1 CR1 ER1 DL0 AL0 CR0 DL1 HR1 AR0,RWL 2 2)::
(makeTM BR1 AR1 CR1 ER1 DL1 AL0 AR0 EL0 HR1 CL0,RWL 3 2)::
(makeTM BR1 AR1 CR1 ER1 DL1 AL0 AR1 EL0 HR1 CL0,RWL 3 2)::
(makeTM BR1 BL0 AL1 CL0 HR1 DL0 DR1 ER0 AR0 CR1,RWL 2 3)::
(makeTM BR1 BL0 AL1 CL0 EL1 DR0 ER1 HR1 CR1 AR0,RWL 6 3)::
(makeTM BR1 BL0 AL1 CL1 AR0 DR1 CR1 ER1 DR0 HR1,RWL 10 2)::
(makeTM BR1 BL0 AL1 CL1 DR0 DL0 ER1 BR1 CR0 HR1,RWL 3 4)::
(makeTM BR1 BL0 AL1 CL1 ER0 DR1 BR1 CR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 BL0 BL1 CL1 DL1 BL0 ER1 HR1 AR1 ER0,RWL 2 2)::
(makeTM BR1 BL0 CL0 BR1 HR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CL0 BR1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CL0 BR1 EL0 DR1 CR0 AL1 DL1 HR1,RWL 13 2)::
(makeTM BR1 BL0 CL0 CL1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CL0 DR0 HR1 AL1 ER0 HR1 EL1 AL0,RWL 3 2)::
(makeTM BR1 BL0 CL0 DR0 HR1 AL1 ER1 AL0 EL1 BL1,RWL 2 3)::
(makeTM BR1 BL0 CL0 DR0 HR1 AL1 ER1 AL1 EL1 DL0,RWL 2 3)::
(makeTM BR1 BL0 CL0 DR0 HR1 AL1 ER1 BR1 EL1 DL0,RWL 2 3)::
(makeTM BR1 BL0 CL0 DR0 HR1 DL1 ER1 AL1 EL1 DL0,RWL 2 3)::
(makeTM BR1 BL0 CL0 DR0 AL1 BL1 ER0 HR1 AR0 BL1,RWL 7 2)::
(makeTM BR1 BL0 CL0 DR0 AL1 BL1 ER0 HR1 AR0 BR1,RWL 7 2)::
(makeTM BR1 BL0 CL0 DR0 AL1 BL1 ER0 HR1 AR0 DR1,RWL 12 2)::
(makeTM BR1 BL0 CL0 DR0 AL1 BL1 ER0 HR1 AR0 EL0,RWL 7 2)::
(makeTM BR1 BL0 CL0 DR0 AL1 CR1 ER1 HR1 CR1 ER0,RWL 36 2)::
(makeTM BR1 BL0 CL0 DR0 AL1 DL0 AR1 EL1 CL0 HR1,RWL 3 3)::
(makeTM BR1 BL0 CL0 DR0 AL1 DL1 AR1 EL0 BL1 HR1,RWL 8 2)::
(makeTM BR1 BL0 CL0 DL1 HR1 DR1 ER1 AR1 AL1 DR0,RWL 5 3)::
(makeTM BR1 BL0 CL0 DL1 AL1 DR1 CR1 ER0 HR1 AL0,RWL 3 2)::
(makeTM BR1 BL0 CL0 DR1 HR1 DR1 BL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CL0 DR1 HR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CL0 DR1 AL1 CR1 CR0 ER1 AR1 HR1,RWL 5 2)::
(makeTM BR1 BL0 CL0 ER0 HR1 DL1 AL1 AL0 DL1 AR1,RWL 2 4)::
(makeTM BR1 BL0 CL0 ER0 AL1 DL0 AR1 BL1 AR1 HR1,RWL 3 3)::
(makeTM BR1 BL0 CL0 ER0 AL1 DL0 BL1 BL1 AR1 HR1,RWL 3 3)::
(makeTM BR1 BL0 CL0 ER0 AL1 DL0 CR1 BL1 AR1 HR1,RWL 3 3)::
(makeTM BR1 BL0 CL0 ER0 AL1 DL0 EL0 BL1 AR1 HR1,RWL 3 3)::
(makeTM BR1 BL0 CL0 ER0 AL1 DL0 ER0 BL1 AR1 HR1,RWL 3 3)::
(makeTM BR1 BL0 CL0 ER0 AL1 DL0 EL1 BL1 AR1 HR1,RWL 3 3)::
(makeTM BR1 BL0 CL0 ER0 AL1 DR0 CR1 HR1 AL1 ER1,RWL 3 2)::
(makeTM BR1 BL0 CL0 ER0 AL1 DR0 CR1 DR0 DR0 HR1,RWL 8 3)::
(makeTM BR1 BL0 CL0 ER0 AR1 DL0 CL1 AL1 CR1 HR1,RWL 6 3)::
(makeTM BR1 BL0 CL0 ER0 CR1 DR1 EL0 HR1 AL1 ER1,RWL 4 2)::
(makeTM BR1 BL0 CL0 ER0 DR1 CL1 HR1 AR1 AL1 ER1,RWL 3 3)::
(makeTM BR1 BL0 CL0 ER0 EL0 DR0 CR1 HR1 AL1 ER1,RWL 4 2)::
(makeTM BR1 BL0 CL0 EL1 HR1 DL1 AL1 DL1 AR0 ER1,RWL 5 3)::
(makeTM BR1 BL0 CL0 EL1 AL1 DR0 CR1 AR0 HR1 DL1,RWL 11 3)::
(makeTM BR1 BL0 CL0 EL1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 BL0 CL0 ER1 AL1 DR0 CR1 AR0 DR1 HR1,RWL 1 4)::
(makeTM BR1 BL0 CL0 ER1 AL1 DR0 CR1 DR0 CL1 HR1,RWL 8 3)::
(makeTM BR1 BL0 CL0 ER1 AL1 DR0 CR1 DR0 DL1 HR1,RWL 8 3)::
(makeTM BR1 BL0 CL0 ER1 AL1 DL1 BL1 DR0 CR1 HR1,RWL 5 2)::
(makeTM BR1 BL0 CR0 AR0 DL0 ER1 BL1 AL1 CR1 HR1,RWL 4 3)::
(makeTM BR1 BL0 CR0 BL1 DL0 CR1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CR0 BL1 DL0 DR1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CR0 BL1 DL1 CR1 EL0 AL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 BL0 CR0 BL1 DL1 CR1 EL0 AL1 HR1 BR0,RWL 2 2)::
(makeTM BR1 BL0 CR0 BL1 DL1 CR1 EL1 AL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 BL0 CR0 BL1 DL1 CR1 EL1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 BL0 CR0 BL1 DL1 CR1 EL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 BL0 CR0 BL1 DL1 CR1 EL1 AL1 HR1 CR1,RWL 2 2)::
(makeTM BR1 BL0 CR0 BL1 DL1 CR1 EL1 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 BL0 CR0 BR1 DL0 CR1 EL1 DL1 HR1 AL1,RWL 2 3)::
(makeTM BR1 BL0 CR0 BR1 DR0 CR0 EL1 HR1 EL1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CR0 CR1 AL1 DR1 HR1 ER0 AL0 ER1,RWL 3 2)::
(makeTM BR1 BL0 CR0 CR1 DL1 ER0 AL0 DL0 BR1 HR1,RWL 12 2)::
(makeTM BR1 BL0 CR0 DL0 DR1 ER0 AL1 BL1 CR1 HR1,RWL 3 2)::
(makeTM BR1 BL0 CR0 DR0 AL1 HR1 CL0 ER1 DL1 AR1,RWL 2 3)::
(makeTM BR1 BL0 CR0 DR0 BL1 AL1 ER0 HR1 EL1 CL0,RWL 3 2)::
(makeTM BR1 BL0 CR0 DR0 CL1 AL1 AR1 ER1 HR1 DR1,RWL 6 2)::
(makeTM BR1 BL0 CR0 DR0 DL1 AL1 AL0 ER0 HR1 BL0,RWL 2 2)::
(makeTM BR1 BL0 CR0 DR0 DL1 AL1 AL0 ER0 HR1 DL1,RWL 2 2)::
(makeTM BR1 BL0 CR0 DR0 DL1 AL1 AL0 ER0 HR1 DR1,RWL 2 2)::
(makeTM BR1 BL0 CR0 EL0 DL1 DR0 AL1 BL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 BL0 CR0 ER0 DL1 HR1 AL1 BL0 CL0 DR0,RWL 4 2)::
(makeTM BR1 BL0 CR0 ER0 DL1 CL1 EL0 HR1 BR0 AL1,RWL 4 2)::
(makeTM BR1 BL0 CR0 EL1 DR0 AL1 DL1 AL0 HR1 DR0,RWL 3 2)::
(makeTM BR1 BL0 CL1 HR1 AL0 DR0 AR0 ER1 AL1 CR0,RWL 4 3)::
(makeTM BR1 BL0 CL1 HR1 AL0 DR0 CR1 ER1 AL1 CR0,RWL 4 2)::
(makeTM BR1 BL0 CL1 AR0 AL0 DR0 ER1 CR1 AR1 HR1,RWL 4 2)::
(makeTM BR1 BL0 CL1 AL1 DR1 CL1 HR1 ER1 CR0 AR1,RWL 6 2)::
(makeTM BR1 BL0 CL1 AL1 DR1 CL1 HR1 ER1 DR1 AR1,RWL 6 2)::
(makeTM BR1 BL0 CL1 BR0 DL0 DL1 AR0 EL1 AL1 HR1,RWL 38 2)::
(makeTM BR1 BL0 CL1 BR0 DL0 DL1 EL1 HR1 AL1 ER0,RWL 10 2)::
(makeTM BR1 BL0 CL1 BR0 DR1 CL0 AL0 ER0 AR0 HR1,RWL 4 3)::
(makeTM BR1 BL0 CL1 BR0 ER0 DL0 CR1 AL0 HR1 AR1,RWL 4 3)::
(makeTM BR1 BL0 CL1 BL1 CR0 DR0 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CL1 BR1 HR1 DL0 ER0 DL1 AL1 ER1,RWL 2 3)::
(makeTM BR1 BL0 CL1 BR1 HR1 DR0 EL0 DR1 AL1 EL1,RWL 2 2)::
(makeTM BR1 BL0 CL1 BR1 HR1 DL1 ER0 DL0 ER1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CL1 BR1 HR1 DL1 ER0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CL1 BR1 HR1 DR1 EL0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CL1 BR1 HR1 DR1 ER0 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CL1 BR1 HR1 DR1 ER0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CL1 BR1 DR0 CL0 DR1 EL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CL1 CR0 HR1 DL0 EL0 DR0 ER1 AR0,RWL 3 2)::
(makeTM BR1 BL0 CL1 CR0 HR1 DL0 EL0 ER1 ER1 AR0,RWL 3 2)::
(makeTM BR1 BL0 CL1 CR0 DL1 CR1 AL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 BL0 CL1 CR0 DR1 AL1 EL0 AR0 HR1 DL1,RWL 5 2)::
(makeTM BR1 BL0 CL1 CR0 EL0 DL0 AR1 BL1 DR0 HR1,RWL 2 3)::
(makeTM BR1 BL0 CL1 CR0 EL1 DR0 HR1 ER0 AL1 CL1,RWL 2 2)::
(makeTM BR1 BL0 CL1 CR0 EL1 DR0 HR1 ER0 AL1 ER1,RWL 3 2)::
(makeTM BR1 BL0 CL1 CR1 AR1 DR1 HR1 ER0 EL1 AR0,RWL 5 2)::
(makeTM BR1 BL0 CL1 CR1 BR1 DR1 HR1 ER0 EL1 AR0,RWL 5 2)::
(makeTM BR1 BL0 CL1 DL0 HR1 AL1 ER0 DL1 BR1 ER1,RWL 2 3)::
(makeTM BR1 BL0 CL1 DL0 HR1 AL1 ER0 DR1 AR1 EL0,RWL 3 2)::
(makeTM BR1 BL0 CL1 DL0 HR1 AL1 ER0 DR1 BL1 ER1,RWL 3 3)::
(makeTM BR1 BL0 CL1 DL0 HR1 AL1 ER1 AR1 DR0 DR1,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR0 HR1 AL1 AL0 ER1 CL0 BL0,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR0 HR1 AL1 AL0 ER1 CL0 DR1,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR0 HR1 AL1 EL0 DR1 BR1 EL1,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR0 HR1 AL1 ER0 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 BL0 CL1 DR0 HR1 BR1 ER0 DL1 EL1 AL0,RWL 3 2)::
(makeTM BR1 BL0 CL1 DR0 HR1 BR1 ER1 AL1 EL1 DL0,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR0 HR1 DR0 ER1 AL1 EL1 DL0,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR0 HR1 DL1 ER1 EL0 AL1 BR1,RWL 2 4)::
(makeTM BR1 BL0 CL1 DR0 AL0 AR1 ER1 HR1 AL1 CR0,RWL 4 2)::
(makeTM BR1 BL0 CL1 DR0 AL0 DR1 ER1 CR1 BR0 HR1,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR0 AL1 CR0 CL0 ER1 CR0 HR1,RWL 4 2)::
(makeTM BR1 BL0 CL1 DR0 CL0 AL1 AR1 ER1 CR1 HR1,RWL 8 2)::
(makeTM BR1 BL0 CL1 DR0 ER1 DL0 AL1 DR1 HR1 CR1,RWL 10 2)::
(makeTM BR1 BL0 CL1 DL1 HR1 AL1 ER0 DL0 ER1 BR1,RWL 2 3)::
(makeTM BR1 BL0 CL1 DL1 HR1 AL1 ER0 DL1 CL1 ER1,RWL 2 2)::
(makeTM BR1 BL0 CL1 DR1 HR1 AL1 BR0 ER0 AL0 BL0,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR1 HR1 AL1 BR0 ER0 EL1 BL0,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR1 HR1 AL1 EL0 DR0 EL1 BR1,RWL 2 2)::
(makeTM BR1 BL0 CL1 DR1 HR1 AR1 BL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CL1 DR1 HR1 AR1 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CL1 DR1 HR1 DL1 ER0 AL0 AR1 AL1,RWL 34 2)::
(makeTM BR1 BL0 CL1 DR1 HR1 DR1 ER0 BL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CL1 DR1 HR1 DR1 ER0 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CL1 DR1 AL1 CL0 BR0 ER0 HR1 CL0,RWL 4 3)::
(makeTM BR1 BL0 CL1 DR1 AR1 BR0 EL1 ER0 HR1 CL0,RWL 3 2)::
(makeTM BR1 BL0 CL1 DR1 CR1 BR0 AL1 ER0 HR1 BL0,RWL 2 3)::
(makeTM BR1 BL0 CL1 DR1 DL1 BL1 BR0 EL0 HR1 AL1,RWL 6 3)::
(makeTM BR1 BL0 CL1 EL0 HR1 DL0 ER1 AL0 AR1 DR1,RWL 2 3)::
(makeTM BR1 BL0 CL1 EL0 DL0 CR0 EL1 HR1 AL1 AR1,RWL 3 2)::
(makeTM BR1 BL0 CL1 ER0 HR1 DL0 EL0 DL1 AL1 ER1,RWL 18 2)::
(makeTM BR1 BL0 CL1 ER0 HR1 DR1 DL1 EL0 DR1 AL1,RWL 2 3)::
(makeTM BR1 BL0 CL1 ER0 AR0 DL0 AR0 AL0 AR1 HR1,RWL 7 3)::
(makeTM BR1 BL0 CL1 ER0 AL1 DL1 CL0 HR1 AR0 BR0,RWL 10 2)::
(makeTM BR1 BL0 CL1 ER0 AR1 DL0 CR1 AL0 AR1 HR1,RWL 4 3)::
(makeTM BR1 BL0 CL1 ER0 AR1 DL0 ER1 AL0 AR1 HR1,RWL 4 3)::
(makeTM BR1 BL0 CL1 ER0 DL1 DR1 AR1 BL0 CR1 HR1,RWL 5 2)::
(makeTM BR1 BL0 CL1 EL1 DR1 CR1 AL0 DL1 HR1 BL0,RWL 2 2)::
(makeTM BR1 BL0 CL1 EL1 ER1 DL1 AL1 CL1 HR1 AR0,RWL 4 2)::
(makeTM BR1 BL0 CL1 ER1 AL0 DR0 HR1 AL1 BR0 CR0,RWL 3 2)::
(makeTM BR1 BL0 CL1 ER1 AL0 DR1 HR1 ER1 BR0 CR0,RWL 3 2)::
(makeTM BR1 BL0 CL1 ER1 DL0 BL1 AL1 HR1 AR0 ER0,RWL 4 2)::
(makeTM BR1 BL0 CL1 ER1 EL1 DR1 HR1 CR0 AL1 ER0,RWL 15 2)::
(makeTM BR1 BL0 CR1 AL0 BL1 DR0 ER1 HR1 AR1 BR0,RWL 4 4)::
(makeTM BR1 BL0 CR1 AR0 CL0 DL0 DR1 ER1 AL1 HR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 AR1 DL1 CL1 ER1 DL0 BR0 HR1,RWL 1 4)::
(makeTM BR1 BL0 CR1 BL1 AL0 DR0 AL1 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 AL0 DR1 ER1 AR0 CR0 HR1,RWL 4 3)::
(makeTM BR1 BL0 CR1 BL1 BL1 DR0 AL1 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 CL0 DR0 AL1 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 DR0 AL0 ER0 HR1 AL1 AR1,RWL 6 3)::
(makeTM BR1 BL0 CR1 BL1 DR0 ER0 BL1 HR1 AL1 ER1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 DR0 ER0 EL1 HR1 AL1 ER1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 DL1 DR0 HR1 ER1 AL1 ER1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 DL1 ER0 AL1 DR1 HR1 DR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 DR1 ER0 AL1 AR0 HR1 DR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 DR1 ER0 AL1 DR1 HR1 DR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 DR1 ER0 BL0 HR1 AL1 ER1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BL1 DR1 ER0 ER0 HR1 AL1 ER1,RWL 2 3)::
(makeTM BR1 BL0 CR1 BR1 DL0 CR0 DL1 EL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CR1 BR1 DL0 CL1 AR1 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 BL0 CR1 BR1 DR0 CR0 DL1 EL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BL0 CR1 CL1 DL0 AR0 EL0 BL1 BR0 HR1,RWL 5 2)::
(makeTM BR1 BL0 CR1 CL1 DL0 AR0 EL1 BL1 CR0 HR1,RWL 5 2)::
(makeTM BR1 BL0 CR1 CL1 DL0 AR0 EL1 BL1 CR1 HR1,RWL 5 2)::
(makeTM BR1 BL0 CR1 CL1 DL0 AR0 EL1 BL1 DR0 HR1,RWL 5 2)::
(makeTM BR1 BL0 CR1 CL1 DL0 AR0 ER1 BL1 DR1 HR1,RWL 5 2)::
(makeTM BR1 BL0 CR1 CL1 DL0 ER1 AL1 DR1 HR1 DR0,RWL 7 2)::
(makeTM BR1 BL0 CR1 CL1 DR1 DL0 EL1 BR0 HR1 AL0,RWL 3 3)::
(makeTM BR1 BL0 CR1 DL0 DR0 HR1 ER1 DR1 AL1 AR0,RWL 3 2)::
(makeTM BR1 BL0 CR1 DL0 DR1 AR0 BL1 ER0 AR1 HR1,RWL 8 2)::
(makeTM BR1 BL0 CR1 DR0 AL0 HR1 EL1 DR1 AL1 ER0,RWL 6 2)::
(makeTM BR1 BL0 CR1 DR0 DL1 AR1 AL0 ER0 HR1 DL1,RWL 1 4)::
(makeTM BR1 BL0 CR1 DR0 DL1 DR0 AL0 ER0 HR1 DL1,RWL 2 2)::
(makeTM BR1 BL0 CR1 DL1 BL1 ER0 AL0 AR1 DR0 HR1,RWL 3 2)::
(makeTM BR1 BL0 CR1 DL1 DR0 HR1 EL1 AR0 BL0 BR0,RWL 3 3)::
(makeTM BR1 BL0 CR1 DL1 DR0 HR1 EL1 AR0 BL0 EL1,RWL 3 3)::
(makeTM BR1 BL0 CR1 DL1 DL1 ER0 AL0 BL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 DR1 CL1 AL1 ER0 BR1 HR1 CR1,RWL 2 2)::
(makeTM BR1 BL0 CR1 DR1 DL1 AL0 CR0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 BL0 CR1 EL0 DR1 BR1 AL1 AR0 HR1 CL0,RWL 2 2)::
(makeTM BR1 BL0 CR1 EL0 DR1 CL1 AL1 AR0 HR1 CL0,RWL 3 2)::
(makeTM BR1 BL0 CR1 ER0 DL0 HR1 AL1 DL1 DR1 AR1,RWL 2 3)::
(makeTM BR1 BL0 CR1 ER0 DL0 AR0 AL1 CL1 AR1 HR1,RWL 9 2)::
(makeTM BR1 BL0 CR1 ER0 DL1 HR1 AL1 DR1 CL0 DR0,RWL 3 3)::
(makeTM BR1 BL0 CR1 ER0 DL1 HR1 EL0 DL0 AL1 ER1,RWL 2 4)::
(makeTM BR1 BL0 CR1 ER0 DL1 AR1 HR1 AL0 AL0 CR0,RWL 4 2)::
(makeTM BR1 BL0 CR1 EL1 DL1 DR0 HR1 BR1 AL0 BL1,RWL 2 3)::
(makeTM BR1 BL0 CR1 EL1 DL1 DR0 AL1 DR1 HR1 BL1,RWL 2 3)::
(makeTM BR1 BL0 CR1 EL1 DR1 HR1 AL1 DR0 DL1 AR0,RWL 4 2)::
(makeTM BR1 BL0 CR1 EL1 DR1 DR0 AL1 DR1 HR1 BL1,RWL 2 3)::
(makeTM BR1 BL0 CR1 ER1 CL0 DR1 DL1 AL0 BR0 HR1,RWL 8 2)::
(makeTM BR1 BL0 CR1 ER1 DR0 HR1 DL1 AL1 AL0 BR0,RWL 8 2)::
(makeTM BR1 BL0 CR1 ER1 DL1 AR1 HR1 AL0 EL1 DR0,RWL 1 4)::
(makeTM BR1 BL0 CR1 ER1 DL1 BR1 HR1 AL0 CL0 DR0,RWL 4 2)::
(makeTM BR1 BL0 CR1 ER1 DL1 BR1 HR1 AL0 EL1 DR0,RWL 4 2)::
(makeTM BR1 BL0 CR1 ER1 DL1 DR1 HR1 AL1 CR0 BR1,RWL 2 2)::
(makeTM BR1 BR0 AL1 CR0 DL0 ER1 EL1 HR1 AR1 EL0,RWL 16 2)::
(makeTM BR1 BR0 AL1 CL1 AL1 DL0 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 BR0 AL1 CL1 BL1 DL0 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 BR0 AL1 CL1 DL0 HR1 DR1 ER0 AL0 BR0,RWL 2 2)::
(makeTM BR1 BR0 BL0 CL1 DL0 EL1 DR1 AR0 BR0 HR1,RWL 2 3)::
(makeTM BR1 BR0 BL1 CL0 DL0 HR1 EL1 AR0 ER1 DR0,RWL 3 3)::
(makeTM BR1 BR0 BL1 CL0 DR1 HR1 DL0 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 BL1 CR0 HR1 DL0 EL1 ER1 DR1 AR1,RWL 5 2)::
(makeTM BR1 BR0 BL1 CR0 DL0 CL1 EL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 BL1 CR0 EL0 DL1 CL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 BL1 CR0 ER1 DL0 CL1 DR0 HR1 AR1,RWL 6 2)::
(makeTM BR1 BR0 BL1 CR0 ER1 DL1 CL0 AR1 DR1 HR1,RWL 1 4)::
(makeTM BR1 BR0 BL1 CL1 CR0 DL0 EL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 BL1 CL1 DL0 AR0 EL1 HR1 CR1 EL1,RWL 1 4)::
(makeTM BR1 BR0 BL1 CL1 DL0 AR0 ER1 CL0 DR1 HR1,RWL 2 3)::
(makeTM BR1 BR0 BL1 CL1 DR0 HR1 EL0 DL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 BL1 CR1 HR1 DL1 EL0 DL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 BL1 CR1 EL0 DL1 HR1 CL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 CL0 AR0 DL1 BL1 EL1 HR1 AL1 CL1,RWL 4 3)::
(makeTM BR1 BR0 CL0 AR0 DR1 CL1 ER1 DL0 AR1 HR1,RWL 9 2)::
(makeTM BR1 BR0 CL0 AR1 HR1 DL0 EL1 DL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 HR1 DR0 EL0 AR1 DR1 EL1,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 HR1 DL1 EL0 DL1 ER1 AR0,RWL 2 3)::
(makeTM BR1 BR0 CL0 BR1 HR1 DL1 ER1 DL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 HR1 DR1 DL1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 BR0 CL0 BR1 HR1 DR1 EL0 AR1 CR1 EL1,RWL 3 2)::
(makeTM BR1 BR0 CL0 BR1 HR1 DR1 EL0 AR1 DR1 EL1,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 DR0 CL1 HR1 EL1 ER1 AR1,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 DR0 CL1 ER1 DL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 DL1 CR0 EL0 HR1 AR1 EL1,RWL 2 3)::
(makeTM BR1 BR0 CL0 BR1 DL1 CL1 ER1 EL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 DR1 CL1 HR1 AR1 HR1 HR1,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 DR1 CL1 HR1 EL0 AR1 ER1,RWL 2 2)::
(makeTM BR1 BR0 CL0 BR1 DR1 CL1 HR1 ER1 AR1 AR1,RWL 3 2)::
(makeTM BR1 BR0 CL0 BR1 DR1 CL1 HR1 ER1 AR1 DL0,RWL 3 2)::
(makeTM BR1 BR0 CL0 BR1 DR1 CL1 HR1 ER1 BL0 AR1,RWL 3 2)::
(makeTM BR1 BR0 CL0 BR1 DR1 CL1 HR1 ER1 CL0 AR1,RWL 3 2)::
(makeTM BR1 BR0 CL0 BR1 DR1 CL1 HR1 ER1 DL1 AR1,RWL 3 2)::
(makeTM BR1 BR0 CL0 CR1 DL1 CR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 BR0 CL0 DL0 AL1 DL1 BL1 ER1 AR0 HR1,RWL 6 2)::
(makeTM BR1 BR0 CL0 DL0 AR1 CL1 EL1 CR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BR0 CL0 DL0 BL1 CR1 EL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 CL0 DR0 ER1 DL1 BL1 EL0 AR0 HR1,RWL 4 3)::
(makeTM BR1 BR0 CL0 DR1 AL1 BL1 ER1 CL1 HR1 AR0,RWL 7 2)::
(makeTM BR1 BR0 CL0 EL0 HR1 DL1 ER1 DL1 AR0 AR1,RWL 2 2)::
(makeTM BR1 BR0 CL0 EL0 DR1 CL1 HR1 AR1 AR0 AR1,RWL 2 2)::
(makeTM BR1 BR0 CL0 ER0 DL1 CR1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 BR0 CL0 ER0 DR1 CL1 HR1 AR1 AL0 AL1,RWL 2 3)::
(makeTM BR1 BR0 CL0 ER1 AR1 DR1 DL1 BL0 CR0 HR1,RWL 9 2)::
(makeTM BR1 BR0 CL0 ER1 DR0 BL0 AR1 HR1 CL1 CR0,RWL 7 2)::
(makeTM BR1 BR0 CL0 ER1 DL1 CR0 AR1 AL0 DR1 HR1,RWL 2 3)::
(makeTM BR1 BR0 CL0 ER1 DR1 CL1 HR1 AR1 CL0 ER1,RWL 2 2)::
(makeTM BR1 BR0 CR0 AR1 DL1 CR0 EL0 HR1 AL1 CL0,RWL 2 2)::
(makeTM BR1 BR0 CR0 BL0 DL1 ER1 BL1 HR1 HR1 AR1,RWL 4 2)::
(makeTM BR1 BR0 CR0 BL1 CL0 DL1 EL0 HR1 ER1 AR0,RWL 2 3)::
(makeTM BR1 BR0 CR0 BL1 CL1 DL1 AR1 EL1 HR1 DL0,RWL 2 3)::
(makeTM BR1 BR0 CR0 BL1 CL1 DL1 EL0 HR1 ER1 AR0,RWL 2 3)::
(makeTM BR1 BR0 CR0 BR1 DL0 AR1 EL0 HR1 CR1 EL1,RWL 2 3)::
(makeTM BR1 BR0 CR0 DL0 AL1 ER1 CL0 BL1 AR1 HR1,RWL 21 2)::
(makeTM BR1 BR0 CR0 DL0 CL1 AL1 EL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 BR0 CR0 DL0 DR1 CL1 EL1 AR1 HR1 CL0,RWL 3 3)::
(makeTM BR1 BR0 CR0 ER1 CL1 DL1 AL1 EL0 HR1 AL0,RWL 4 2)::
(makeTM BR1 BR0 CL1 AL0 DL0 AL1 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 BR0 CL1 AL0 DL0 BL1 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 BR0 CL1 AL0 DL0 CL1 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 BR0 CL1 AR0 DL0 BL1 EL1 HR1 AL1 EL1,RWL 4 3)::
(makeTM BR1 BR0 CL1 AR0 DR1 BL0 HR1 ER1 AR1 CR1,RWL 6 2)::
(makeTM BR1 BR0 CL1 AR0 EL1 DL1 BL0 DL0 AR1 HR1,RWL 28 2)::
(makeTM BR1 BR0 CL1 AR1 HR1 DL0 EL1 DL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 BR0 CL1 AR1 HR1 DL1 EL1 DL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 BR0 CL1 AR1 HR1 DR1 EL1 DL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 BR0 CL1 AR1 DL0 AL1 ER1 BL0 DR1 HR1,RWL 12 2)::
(makeTM BR1 BR0 CL1 AR1 EL0 DL1 AR1 CL0 HR1 AL1,RWL 8 2)::
(makeTM BR1 BR0 CL1 BR1 HR1 DL0 AR1 DL1 HR1 HR1,RWL 2 3)::
(makeTM BR1 BR0 CL1 BR1 HR1 DL0 AR1 EL1 HR1 DL1,RWL 2 3)::
(makeTM BR1 BR0 CL1 BR1 HR1 DL0 AR1 EL1 AR1 EL1,RWL 2 3)::
(makeTM BR1 BR0 CL1 BR1 HR1 DR0 EL0 DL1 AR1 EL1,RWL 2 3)::
(makeTM BR1 BR0 CL1 BR1 HR1 DL1 EL1 EL0 AR1 EL1,RWL 3 3)::
(makeTM BR1 BR0 CL1 BR1 HR1 DL1 ER1 EL0 AR1 EL1,RWL 3 3)::
(makeTM BR1 BR0 CL1 BR1 DL1 DL0 AR1 EL0 HR1 BR0,RWL 2 3)::
(makeTM BR1 BR0 CL1 CR0 AL0 DL0 AR1 EL1 HR1 DL1,RWL 2 3)::
(makeTM BR1 BR0 CL1 CR0 DR0 DL1 AR1 EL1 AL0 HR1,RWL 2 4)::
(makeTM BR1 BR0 CL1 CR0 DL1 AL1 EL0 HR1 AR1 EL1,RWL 2 3)::
(makeTM BR1 BR0 CL1 CR0 EL0 DL0 AR1 DL1 BR1 HR1,RWL 2 3)::
(makeTM BR1 BR0 CL1 CR0 EL1 DL0 AR1 DL1 DL0 HR1,RWL 2 3)::
(makeTM BR1 BR0 CL1 DL0 HR1 AL1 AR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 CL1 DL0 HR1 AL1 EL0 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 CL1 DL0 HR1 AL1 ER1 DL1 EL0 AR0,RWL 2 4)::
(makeTM BR1 BR0 CL1 DL0 HR1 DR1 EL0 BL1 ER1 AR0,RWL 3 2)::
(makeTM BR1 BR0 CL1 DL0 BL1 DL1 AL1 ER1 AR0 HR1,RWL 5 2)::
(makeTM BR1 BR0 CL1 DL0 CL1 DL1 AL1 ER1 AR0 HR1,RWL 5 2)::
(makeTM BR1 BR0 CL1 DL0 DR1 AL1 BL0 ER0 AR1 HR1,RWL 3 3)::
(makeTM BR1 BR0 CL1 DL0 EL1 AL1 AR0 DL1 AR1 HR1,RWL 1 3)::
(makeTM BR1 BR0 CL1 DR0 AL0 AR1 HR1 ER0 EL1 CL0,RWL 1 4)::
(makeTM BR1 BR0 CL1 DR0 AR1 DL1 EL1 BL0 CL0 HR1,RWL 3 2)::
(makeTM BR1 BR0 CL1 DR0 DL0 CL1 ER1 DL0 AR1 HR1,RWL 3 3)::
(makeTM BR1 BR0 CL1 DR0 EL0 DR0 HR1 BL1 ER1 AR0,RWL 2 3)::
(makeTM BR1 BR0 CL1 DR0 EL0 DR1 HR1 BL1 ER1 AR0,RWL 2 3)::
(makeTM BR1 BR0 CL1 DL1 DR1 BL1 EL0 AR0 AL0 HR1,RWL 6 2)::
(makeTM BR1 BR0 CL1 DL1 EL1 BR1 ER0 AR1 HR1 AL0,RWL 2 2)::
(makeTM BR1 BR0 CL1 DR1 HR1 AL1 BR0 ER0 EL1 BL0,RWL 2 3)::
(makeTM BR1 BR0 CL1 DR1 HR1 AL1 CR1 ER0 EL1 BL0,RWL 2 3)::
(makeTM BR1 BR0 CL1 DR1 HR1 DL0 AR1 EL0 ER1 AR1,RWL 4 2)::
(makeTM BR1 BR0 CL1 DR1 AL0 AR1 EL1 CL0 HR1 DL0,RWL 2 4)::
(makeTM BR1 BR0 CL1 DR1 AR1 BR0 EL1 ER0 HR1 BL0,RWL 2 3)::
(makeTM BR1 BR0 CL1 EL0 HR1 DL0 AR1 DL1 AR0 AR1,RWL 2 3)::
(makeTM BR1 BR0 CL1 EL0 CL0 DL0 AL1 HR1 AR0 ER1,RWL 2 3)::
(makeTM BR1 BR0 CL1 EL0 DL0 BL1 AR0 HR1 AL1 DR1,RWL 5 3)::
(makeTM BR1 BR0 CL1 EL0 DL1 BL1 AR1 HR1 AR0 EL1,RWL 1 3)::
(makeTM BR1 BR0 CL1 EL0 DL1 CR1 AL1 AR0 AL0 HR1,RWL 2 3)::
(makeTM BR1 BR0 CL1 EL0 DR1 BL1 HR1 AR0 AR1 DL0,RWL 4 2)::
(makeTM BR1 BR0 CL1 ER0 HR1 DL0 AR1 DL1 AL0 AL1,RWL 2 3)::
(makeTM BR1 BR0 CL1 ER0 HR1 DL0 AR1 DL1 AL0 DL0,RWL 2 3)::
(makeTM BR1 BR0 CL1 ER0 HR1 DL1 AR1 DL0 AR1 DR1,RWL 4 2)::
(makeTM BR1 BR0 CL1 ER0 HR1 DL1 AR1 DL0 DR0 DR1,RWL 8 3)::
(makeTM BR1 BR0 CL1 ER0 DL0 CL1 DR1 AR0 HR1 AL0,RWL 2 3)::
(makeTM BR1 BR0 CL1 ER0 DL0 CL1 DR1 AR0 HR1 BL1,RWL 2 3)::
(makeTM BR1 BR0 CL1 EL1 DL1 AR1 HR1 AL0 BR1 DR0,RWL 2 2)::
(makeTM BR1 BR0 CL1 EL1 DL1 AR1 HR1 AL0 CL0 DR0,RWL 2 2)::
(makeTM BR1 BR0 CL1 ER1 HR1 DL0 AR1 DL1 CL1 BR1,RWL 2 3)::
(makeTM BR1 BR0 CL1 ER1 HR1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 BR0 CL1 ER1 HR1 DL0 AR1 DL1 EL0 BR1,RWL 2 3)::
(makeTM BR1 BR0 CL1 ER1 AL0 DL1 BR0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 BR0 CL1 ER1 AL0 DL1 BR0 DR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 BR0 CL1 ER1 AL0 DL1 BR0 DR1 HR1 DL0,RWL 2 2)::
(makeTM BR1 BR0 CL1 ER1 AR1 DL0 EL0 HR1 BL1 AR0,RWL 11 2)::
(makeTM BR1 BR0 CL1 ER1 DL0 CL0 DR1 AR0 HR1 CR1,RWL 5 3)::
(makeTM BR1 BR0 CL1 ER1 DL0 CL1 DR1 AR0 HR1 CL1,RWL 2 3)::
(makeTM BR1 BR0 CL1 ER1 DL1 CL1 AR1 DR1 HR1 AR1,RWL 3 2)::
(makeTM BR1 BR0 CL1 ER1 DL1 CL1 AR1 DR1 HR1 DL0,RWL 3 2)::
(makeTM BR1 BR0 CL1 ER1 DR1 BL0 AR1 DR0 CR0 HR1,RWL 4 2)::
(makeTM BR1 BR0 CL1 ER1 ER0 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 BR0 CR1 HR1 CL1 DR1 AL0 EL1 AR1 DL0,RWL 6 2)::
(makeTM BR1 BR0 CR1 HR1 DR1 CR0 EL1 CL0 AR1 DL0,RWL 2 3)::
(makeTM BR1 BR0 CR1 BR1 CL0 DL0 ER1 DL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 BR0 CR1 BR1 DL1 CL1 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 BR0 CR1 BR1 DL1 EL0 HR1 CL1 AR1 EL1,RWL 1 2)::
(makeTM BR1 BR0 CR1 CL1 DL1 AR1 HR1 EL0 AL0 AL1,RWL 9 2)::
(makeTM BR1 BR0 CR1 DL0 AL1 AR0 EL0 HR1 AR1 EL1,RWL 1 4)::
(makeTM BR1 BR0 CR1 DL0 AL1 CL1 EL1 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 BR0 CR1 DL0 AL1 CL1 EL1 AR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 BR0 CR1 DL0 DR1 ER1 BL1 CL0 AR0 HR1,RWL 4 2)::
(makeTM BR1 BR0 CR1 EL0 DL1 AR1 AR0 CL0 HR1 CL1,RWL 3 2)::
(makeTM BR1 BR0 CR1 EL0 DL1 AR1 BL1 CL0 HR1 CL1,RWL 3 2)::
(makeTM BR1 BL1 AL1 CR0 HR1 DR1 EL0 DL1 AL0 AR1,RWL 1 4)::
(makeTM BR1 BL1 AL1 CR0 CL1 DL0 BR0 EL1 HR1 DL1,RWL 2 3)::
(makeTM BR1 BL1 AL1 CL1 HR1 DL0 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 BL1 AL1 CL1 HR1 DL0 DR1 EL0 BR1 ER0,RWL 5 2)::
(makeTM BR1 BL1 AL1 CL1 HR1 DL0 ER1 EL0 DR1 AR0,RWL 5 2)::
(makeTM BR1 BL1 AL1 CL1 BR1 DL0 DR1 EL0 HR1 CR0,RWL 5 2)::
(makeTM BR1 BL1 AL1 CL1 DL0 BR0 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 BL1 AL1 CL1 DR1 DL0 CR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 BL1 BL1 CL0 CR1 DR0 AL0 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR1 BL1 CL0 BL0 DL1 DR1 ER1 HR1 AL1 AR0,RWL 4 2)::
(makeTM BR1 BL1 CL0 BR1 DR1 CL1 HR1 ER1 AL1 BR0,RWL 2 2)::
(makeTM BR1 BL1 CL0 CR0 AR1 DL0 AL1 ER0 DR1 HR1,RWL 3 3)::
(makeTM BR1 BL1 CL0 DR0 HR1 AL1 ER0 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 BL1 CL0 DR0 HR1 AL1 ER1 AL0 CL1 DR1,RWL 2 3)::
(makeTM BR1 BL1 CL0 DR0 AL1 BL0 ER0 HR1 EL1 AR0,RWL 3 2)::
(makeTM BR1 BL1 CL0 DR0 EL0 AL1 AR1 AL0 AR0 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL0 DR0 EL1 AL1 AR1 AL0 BR0 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL0 DR0 EL1 AL1 AR1 AL0 BR1 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL0 DR0 EL1 AL1 AR1 AL0 CR0 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL0 DR0 EL1 AL1 AR1 AL0 DL0 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL0 DR0 EL1 AL1 AR1 EL0 BR1 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL0 DR1 HR1 DR1 BL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL0 DR1 HR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL0 DR1 AL1 BR0 AR1 ER0 HR1 CR1,RWL 4 2)::
(makeTM BR1 BL1 CL0 DR1 AR1 CL1 BR0 EL0 HR1 AL1,RWL 23 2)::
(makeTM BR1 BL1 CL0 ER0 HR1 DR0 AL1 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL0 ER0 HR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL0 ER0 HR1 DR1 DL1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL0 ER0 DL1 CL0 AL1 DR1 HR1 AR0,RWL 2 3)::
(makeTM BR1 BL1 CL0 ER0 DL1 CL1 AL1 DR1 HR1 AR0,RWL 2 3)::
(makeTM BR1 BL1 CL0 ER0 DL1 CR1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL0 ER0 EL0 DL1 AL1 HR1 AR0 CL1,RWL 3 4)::
(makeTM BR1 BL1 CR0 HR1 CL1 DL0 ER0 DL1 AL0 AR0,RWL 2 3)::
(makeTM BR1 BL1 CR0 BR0 CL1 DL0 EL1 DR0 AL1 HR1,RWL 1 4)::
(makeTM BR1 BL1 CR0 BR1 CL1 DL0 AL1 EL0 HR1 BR0,RWL 3 2)::
(makeTM BR1 BL1 CR0 CR1 DL1 EL0 AL0 HR1 AR1 DR0,RWL 3 2)::
(makeTM BR1 BL1 CR0 DL0 AL1 DR1 CR1 EL1 HR1 AL0,RWL 4 3)::
(makeTM BR1 BL1 CR0 DL0 CL1 AR1 ER1 AL0 DR0 HR1,RWL 8 2)::
(makeTM BR1 BL1 CR0 DR0 AL1 EL0 CL1 AR0 CL1 HR1,RWL 3 2)::
(makeTM BR1 BL1 CR0 DL1 CL1 AL0 ER0 EL0 HR1 BR0,RWL 4 2)::
(makeTM BR1 BL1 CR0 ER0 DL1 AL1 AL0 HR1 CR1 AL0,RWL 2 3)::
(makeTM BR1 BL1 CR0 EL1 CL1 DR1 HR1 AR1 BR1 EL0,RWL 4 2)::
(makeTM BR1 BL1 CL1 HR1 DR1 DL0 EL1 ER1 AR0 ER0,RWL 4 2)::
(makeTM BR1 BL1 CL1 HR1 ER1 DR0 DL1 BL0 AL1 CR0,RWL 14 2)::
(makeTM BR1 BL1 CL1 BR0 AL0 DL0 DR0 EL1 BR1 HR1,RWL 6 3)::
(makeTM BR1 BL1 CL1 BR0 AL0 DL0 ER0 AL1 DR0 HR1,RWL 6 3)::
(makeTM BR1 BL1 CL1 BR0 AL0 DR0 AR0 EL1 DL0 HR1,RWL 12 3)::
(makeTM BR1 BL1 CL1 BR0 DL1 CR1 AL0 EL1 HR1 BR1,RWL 2 4)::
(makeTM BR1 BL1 CL1 BR0 EL0 DL0 EL0 HR1 AL1 AR0,RWL 4 2)::
(makeTM BR1 BL1 CL1 BR0 EL0 DL0 EL1 HR1 AL1 AR0,RWL 5 3)::
(makeTM BR1 BL1 CL1 BR0 EL0 DL1 CL0 HR1 AL1 AR0,RWL 4 2)::
(makeTM BR1 BL1 CL1 BR0 EL1 DR1 BL1 DR1 AL0 HR1,RWL 2 4)::
(makeTM BR1 BL1 CL1 BR1 HR1 DL0 ER1 DL1 AR1 BR0,RWL 2 3)::
(makeTM BR1 BL1 CL1 BR1 HR1 DL1 AR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 BL1 CL1 CR0 DL1 CR1 EL0 BR0 AL0 HR1,RWL 6 3)::
(makeTM BR1 BL1 CL1 CR0 DR1 DL0 AR1 EL1 HR1 AL1,RWL 1 4)::
(makeTM BR1 BL1 CL1 DR0 HR1 AL1 HR1 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 BL1 CL1 DR0 HR1 BR1 ER1 AL0 EL1 DL0,RWL 2 3)::
(makeTM BR1 BL1 CL1 DR0 HR1 DL0 AL1 ER1 AR0 ER1,RWL 1 3)::
(makeTM BR1 BL1 CL1 DR0 HR1 DL1 BR1 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 BL1 CL1 DR0 BR1 AL1 HR1 ER0 EL1 CL0,RWL 3 2)::
(makeTM BR1 BL1 CL1 DR0 DL0 DR0 AR1 EL0 AL1 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL1 DR0 DL1 DR0 AR1 EL0 AL1 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL1 DR0 EL0 DR0 AR1 EL0 AL1 HR1,RWL 5 2)::
(makeTM BR1 BL1 CL1 DR0 EL0 DR1 HR1 ER0 BR0 AL0,RWL 3 2)::
(makeTM BR1 BL1 CL1 DR0 ER1 AR1 HR1 BL0 AL1 CR0,RWL 9 2)::
(makeTM BR1 BL1 CL1 DR1 HR1 AR1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL1 DR1 HR1 AR1 ER0 BL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL1 DR1 HR1 DR1 ER0 BL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL1 DR1 HR1 DR1 ER0 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL1 DR1 AL0 AL1 HR1 ER0 AR1 CL1,RWL 12 2)::
(makeTM BR1 BL1 CL1 EL0 HR1 DL1 ER1 AR0 AR1 DL0,RWL 2 3)::
(makeTM BR1 BL1 CL1 ER0 HR1 DL0 AR0 AR1 EL1 AL0,RWL 2 3)::
(makeTM BR1 BL1 CL1 ER0 HR1 DL0 AL1 EL0 BR1 AL1,RWL 10 2)::
(makeTM BR1 BL1 CL1 ER0 HR1 DR0 HR1 AL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL1 ER0 HR1 DR0 BR1 DL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL1 ER0 HR1 DL1 DR1 BR0 EL1 AL0,RWL 3 2)::
(makeTM BR1 BL1 CL1 ER0 HR1 DR1 ER0 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL1 ER0 AR1 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 BL1 CL1 EL1 DR1 CR1 AL1 DL1 HR1 AL0,RWL 3 2)::
(makeTM BR1 BL1 CL1 ER1 HR1 DL0 AL1 AR0 DR1 CL0,RWL 3 3)::
(makeTM BR1 BL1 CL1 ER1 AR1 DL0 DR1 BR0 HR1 CL1,RWL 2 2)::
(makeTM BR1 BL1 CL1 ER1 DL1 CR0 AL1 AL0 HR1 CR1,RWL 15 2)::
(makeTM BR1 BL1 CL1 ER1 DR1 CL0 AL0 DR0 HR1 BR0,RWL 2 3)::
(makeTM BR1 BL1 CR1 AR0 AL1 DL1 EL0 CL0 HR1 BR0,RWL 5 2)::
(makeTM BR1 BL1 CR1 AR0 AL1 DL1 EL1 CL0 HR1 BR0,RWL 5 2)::
(makeTM BR1 BL1 CR1 BL0 AL1 DR0 HR1 ER0 AL0 AR1,RWL 6 2)::
(makeTM BR1 BL1 CR1 BL0 AL1 DR0 HR1 ER0 EL1 AR1,RWL 15 2)::
(makeTM BR1 BL1 CR1 BL0 DR0 DR1 ER1 HR1 AL0 AR0,RWL 10 2)::
(makeTM BR1 BL1 CR1 BL0 DR1 AR0 AL1 ER0 HR1 CR0,RWL 16 3)::
(makeTM BR1 BL1 CR1 BL0 DR1 CR1 AL1 ER0 HR1 AR0,RWL 8 3)::
(makeTM BR1 BL1 CR1 BL1 AL0 DR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 BL1 CR1 BL1 BL0 DR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 BL1 CR1 BL1 DL0 ER1 AL0 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 BL1 CR1 DL0 AL0 ER1 BL0 AR0 CR0 HR1,RWL 7 3)::
(makeTM BR1 BL1 CR1 DL0 AL0 ER1 ER0 BL0 CR0 HR1,RWL 12 2)::
(makeTM BR1 BL1 CR1 DL0 DL0 AR0 HR1 EL1 AR0 AL1,RWL 6 2)::
(makeTM BR1 BL1 CR1 DR0 AL1 CL0 ER0 CL1 AR0 HR1,RWL 2 3)::
(makeTM BR1 BL1 CR1 DR0 AL1 ER1 CL1 CL0 HR1 AR0,RWL 4 2)::
(makeTM BR1 BL1 CR1 DR0 BL0 HR1 ER1 AL0 EL1 DL0,RWL 2 3)::
(makeTM BR1 BL1 CR1 DR0 DL0 ER1 CL1 AL1 HR1 BR1,RWL 1 4)::
(makeTM BR1 BL1 CR1 DR0 DR1 HR1 EL1 AL0 DL0 BL0,RWL 2 3)::
(makeTM BR1 BL1 CR1 DL1 AL0 CR0 EL1 AR1 BL0 HR1,RWL 4 2)::
(makeTM BR1 BL1 CR1 DL1 AL0 CR0 EL1 DL1 BL0 HR1,RWL 4 2)::
(makeTM BR1 BL1 CR1 DL1 AL1 DR0 EL0 AL0 BR0 HR1,RWL 6 3)::
(makeTM BR1 BL1 CR1 DR1 AL1 CL0 ER0 BR0 BR0 HR1,RWL 3 3)::
(makeTM BR1 BL1 CR1 EL0 DR0 CL1 AL1 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR1 BL1 CR1 EL0 DL1 CR0 EL1 DL1 AL0 HR1,RWL 10 2)::
(makeTM BR1 BL1 CR1 EL0 DR1 CR1 AL0 DL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 BL1 CR1 EL0 DR1 CR1 AL0 DL1 HR1 DR1,RWL 2 2)::
(makeTM BR1 BL1 CR1 EL0 DR1 ER1 EL1 HR1 AR0 BL0,RWL 4 3)::
(makeTM BR1 BL1 CR1 ER0 DL0 BR1 EL1 DR1 HR1 AL0,RWL 3 2)::
(makeTM BR1 BL1 CR1 ER0 DR0 HR1 DL1 EL0 BL1 AL0,RWL 2 3)::
(makeTM BR1 BL1 CR1 ER0 DL1 BR1 HR1 AL0 DR0 EL1,RWL 3 2)::
(makeTM BR1 BL1 CR1 ER0 DL1 BR1 DR0 AL0 HR1 DL1,RWL 3 2)::
(makeTM BR1 BL1 CR1 EL1 DL1 AR0 BL1 DL1 HR1 BL0,RWL 2 2)::
(makeTM BR1 BL1 CR1 EL1 DL1 BR0 HR1 AL1 AL0 DL1,RWL 4 2)::
(makeTM BR1 BL1 CR1 EL1 DR1 CR1 AL0 DL1 HR1 BL0,RWL 2 2)::
(makeTM BR1 BL1 CR1 EL1 DR1 CR1 AL1 DL1 HR1 AL0,RWL 3 2)::
(makeTM BR1 BL1 CR1 ER1 DL1 BR0 HR1 CL1 AL0 EL1,RWL 6 2)::
(makeTM BR1 BL1 CR1 ER1 DL1 DR0 AL1 AL0 HR1 CL1,RWL 2 3)::
(makeTM BR1 BL1 CR1 ER1 DL1 ER1 HR1 CL1 BR0 AL0,RWL 8 2)::
(makeTM BR1 BR1 AL1 CR0 CL1 DL0 BR0 EL1 HR1 DL1,RWL 2 3)::
(makeTM BR1 BR1 AL1 CL1 HR1 DL0 DR1 ER0 AL0 CR1,RWL 2 2)::
(makeTM BR1 BR1 AL1 CR1 CL1 DL0 HR1 EL0 ER1 BR0,RWL 3 2)::
(makeTM BR1 BR1 BL1 CL1 DL0 BR0 DR1 EL1 HR1 AR0,RWL 2 3)::
(makeTM BR1 BR1 CL0 BR1 DR1 CL1 HR1 ER1 AL1 BR0,RWL 2 2)::
(makeTM BR1 BR1 CR0 DL1 AL1 ER0 HR1 AL0 EL1 BL0,RWL 3 2)::
(makeTM BR1 BR1 CR0 DR1 DL0 AR0 EL1 HR1 AR1 EL0,RWL 3 3)::
(makeTM BR1 BR1 CR0 EL0 DR1 AR0 BL1 BR0 DL1 HR1,RWL 3 3)::
(makeTM BR1 BR1 CR0 EL1 DL1 BR0 BL0 HR1 AL0 CL1,RWL 4 2)::
(makeTM BR1 BR1 CL1 AL0 HR1 DL0 DR1 ER0 AL1 BR0,RWL 2 2)::
(makeTM BR1 BR1 CL1 AL0 HR1 DL0 DR1 ER0 AL1 CR1,RWL 2 2)::
(makeTM BR1 BR1 CL1 BR1 HR1 DL0 ER1 DL1 AL1 BR0,RWL 2 3)::
(makeTM BR1 BR1 CL1 BR1 HR1 DL0 ER1 DL1 AR1 BR0,RWL 2 3)::
(makeTM BR1 BR1 CL1 BR1 HR1 DL1 AR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 BR1 CL1 CR0 DL0 CR1 ER1 DL1 HR1 AR1,RWL 3 2)::
(makeTM BR1 BR1 CL1 CR1 ER1 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 BR1 CL1 DR0 AL1 BL1 AR0 EL1 DL0 HR1,RWL 9 2)::
(makeTM BR1 BR1 CL1 DR1 CR1 DL0 CL0 ER1 AR0 HR1,RWL 4 2)::
(makeTM BR1 BR1 CL1 EL0 DR0 BL1 AR0 DR1 HR1 CL1,RWL 6 4)::
(makeTM BR1 BR1 CL1 ER0 DL0 CL0 DR1 AR0 HR1 CR1,RWL 3 3)::
(makeTM BR1 BR1 CL1 ER0 DL1 CL1 AR1 DR1 HR1 AR1,RWL 3 2)::
(makeTM BR1 BR1 CL1 ER0 DR1 CL1 HR1 AR1 CL0 ER1,RWL 3 2)::
(makeTM BR1 BR1 CL1 ER0 ER1 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 BR1 CL1 ER1 DL1 CL1 AR1 DR1 HR1 AR0,RWL 3 2)::
(makeTM BR1 BR1 CL1 ER1 DR1 BL0 HR1 AR1 AR0 DR1,RWL 4 2)::
(makeTM BR1 BR1 CL1 ER1 ER0 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 BR1 CL1 ER1 ER1 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 BR1 CR1 HR1 DL1 EL0 AR1 CL0 ER1 BR0,RWL 14 2)::
(makeTM BR1 BR1 CR1 CR0 DL0 CR1 ER1 DL1 HR1 AR1,RWL 3 2)::
(makeTM BR1 CL0 AL0 HR1 DR0 CL1 EL1 DR1 CL1 AL1,RWL 2 2)::
(makeTM BR1 CL0 AL0 HR1 DR0 CL1 EL1 DR1 CR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 AL0 HR1 DR0 CL1 EL1 DR1 DR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 AL0 HR1 DR1 CL1 CL1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 AL0 DR0 AL1 BR0 ER0 HR1 CR1 EL1,RWL 4 2)::
(makeTM BR1 CL0 AL0 DR0 AL1 CL1 DL1 ER0 HR1 CR1,RWL 2 3)::
(makeTM BR1 CL0 AL0 DR0 AL1 EL0 ER1 HR1 CR1 ER0,RWL 2 3)::
(makeTM BR1 CL0 AL0 DR1 AL1 EL0 ER0 HR1 CR1 AR0,RWL 6 2)::
(makeTM BR1 CL0 AL0 DR1 AL1 ER1 BR0 AL0 DR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 AL0 DR1 AL1 ER1 BR0 DL0 DR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 AL1 HR1 CR1 DR0 AL0 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 HR1 CR1 DR0 EL0 DR1 BR1 AL1,RWL 2 3)::
(makeTM BR1 CL0 AL1 HR1 DR1 CL1 EL1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 AL1 HR1 DR1 CL1 ER1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 AL1 HR1 DR1 DL0 ER0 AR0 AL0 ER1,RWL 2 2)::
(makeTM BR1 CL0 AL1 BR1 DR0 CL1 BL1 ER1 HR1 BR0,RWL 6 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 CL1 BL1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 CL1 BR1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 CL1 CL1 ER1 HR1 BR0,RWL 3 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 CL1 CR1 ER1 HR1 BR0,RWL 3 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 CL1 EL1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 CL1 ER1 ER0 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 EL1 BL1 BR0 HR1 CL1,RWL 2 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 EL1 BR1 BR0 HR1 CL1,RWL 2 3)::
(makeTM BR1 CL0 AL1 BR1 DR1 EL1 DL0 BR0 HR1 CL1,RWL 2 3)::
(makeTM BR1 CL0 AL1 CR0 DR1 EL1 BL1 AR0 DL0 HR1,RWL 2 2)::
(makeTM BR1 CL0 AL1 CR1 AR1 DR0 BL1 ER0 HR1 AL0,RWL 6 2)::
(makeTM BR1 CL0 AL1 CR1 AR1 DR0 BL1 ER1 HR1 AL1,RWL 6 2)::
(makeTM BR1 CL0 AL1 CR1 AR1 DR1 EL1 ER0 HR1 AL1,RWL 6 2)::
(makeTM BR1 CL0 AL1 DL0 BL0 HR1 ER1 DR0 AR0 EL0,RWL 3 2)::
(makeTM BR1 CL0 AL1 DL0 BL1 HR1 EL1 ER0 DR1 AR0,RWL 6 3)::
(makeTM BR1 CL0 AL1 DR0 AL1 EL0 ER1 HR1 CR1 ER0,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR0 BL0 ER0 CR0 HR1 AL0 AR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR0 BL0 ER0 CR0 HR1 AL0 ER1,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR0 BR0 BR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR0 BR0 ER0 AL0 CR1 DL0 HR1,RWL 6 2)::
(makeTM BR1 CL0 AL1 DR0 BL1 DL1 EL0 AR0 AR1 HR1,RWL 3 2)::
(makeTM BR1 CL0 AL1 DR0 BL1 ER0 HR1 CR0 AL0 AR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR0 BL1 ER0 HR1 CR0 AL0 ER1,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR0 BL1 EL1 HR1 CR0 DR1 AR0,RWL 8 3)::
(makeTM BR1 CL0 AL1 DR0 BL1 EL1 HR1 CR0 DR1 BL1,RWL 5 3)::
(makeTM BR1 CL0 AL1 DR0 CR1 BR1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR0 DR1 EL1 ER1 HR1 AR0 AL0,RWL 8 2)::
(makeTM BR1 CL0 AL1 DL1 BL0 AR0 CR1 ER0 HR1 DR0,RWL 2 4)::
(makeTM BR1 CL0 AL1 DL1 CR1 BR0 DR0 ER0 HR1 AL0,RWL 2 2)::
(makeTM BR1 CL0 AL1 DL1 CR1 BR0 DR0 ER1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 AL1 DL1 CR1 DR0 AL1 ER0 HR1 AL0,RWL 2 2)::
(makeTM BR1 CL0 AL1 DL1 CR1 DR0 AL1 ER1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 AL1 DR1 AL1 CL0 ER0 HR1 AR0 ER1,RWL 8 3)::
(makeTM BR1 CL0 AL1 DR1 AL1 DL1 ER0 CR0 HR1 CR1,RWL 9 2)::
(makeTM BR1 CL0 AL1 DR1 AL1 EL0 CR1 HR1 ER1 DR0,RWL 14 2)::
(makeTM BR1 CL0 AL1 DR1 BL0 EL0 CR0 HR1 DR0 AR0,RWL 6 2)::
(makeTM BR1 CL0 AL1 DR1 BL0 ER0 DL1 CL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR1 BR0 BR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 CL0 AL1 DR1 BR0 ER0 HR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR1 BR0 EL1 HR1 BR1 DR0 CL1,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR1 BL1 EL0 HR1 ER0 CL1 ER0,RWL 4 2)::
(makeTM BR1 CL0 AL1 DR1 CR1 BR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 CL0 AL1 DR1 CR1 BR1 HR1 ER0 BL1 ER1,RWL 2 2)::
(makeTM BR1 CL0 AL1 DR1 CR1 BR1 HR1 ER0 BR1 ER1,RWL 2 2)::
(makeTM BR1 CL0 AL1 DR1 CR1 BR1 HR1 EL1 CL0 EL0,RWL 2 2)::
(makeTM BR1 CL0 AL1 DR1 CR1 BR1 HR1 EL1 CR0 EL0,RWL 2 2)::
(makeTM BR1 CL0 AL1 DR1 CR1 BR1 HR1 ER1 CL0 EL0,RWL 2 2)::
(makeTM BR1 CL0 AL1 DR1 CR1 DR0 AL0 ER0 HR1 AL1,RWL 2 3)::
(makeTM BR1 CL0 AL1 DR1 DL1 EL0 CR1 BL0 HR1 DR0,RWL 3 2)::
(makeTM BR1 CL0 AL1 EL0 DL0 HR1 ER0 BR0 BL1 DR1,RWL 6 2)::
(makeTM BR1 CL0 AL1 ER0 CR1 DL0 HR1 EL1 BR1 ER1,RWL 2 3)::
(makeTM BR1 CL0 AL1 ER0 CR1 DL1 AL1 DR1 HR1 DR0,RWL 3 4)::
(makeTM BR1 CL0 AL1 ER0 DL0 DR1 AL1 AR0 CR0 HR1,RWL 2 3)::
(makeTM BR1 CL0 AL1 ER0 DR0 BL0 BL1 HR1 AR1 CR1,RWL 3 2)::
(makeTM BR1 CL0 AL1 ER0 DR0 BL0 CR1 HR1 AR1 BR0,RWL 3 3)::
(makeTM BR1 CL0 AL1 ER0 DL1 HR1 BL0 BR0 CL1 DR1,RWL 8 2)::
(makeTM BR1 CL0 AL1 ER0 DL1 HR1 EL1 BL0 BL1 BR0,RWL 8 2)::
(makeTM BR1 CL0 AL1 ER0 DL1 HR1 EL1 DL0 BR1 DR0,RWL 2 3)::
(makeTM BR1 CL0 AL1 ER0 DL1 BL0 AL1 HR1 CR0 AR0,RWL 3 2)::
(makeTM BR1 CL0 AL1 ER0 DL1 BR1 DR1 CR0 HR1 CL0,RWL 2 3)::
(makeTM BR1 CL0 AL1 ER0 DL1 DR1 AL1 AR0 HR1 CR0,RWL 3 2)::
(makeTM BR1 CL0 AL1 ER1 DR0 CL1 AL1 DR1 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL0 BL0 CR0 DL1 AR0 EL0 HR1 AL1 EL1,RWL 2 3)::
(makeTM BR1 CL0 BL0 CL1 CR1 DR0 ER0 HR1 EL1 AL0,RWL 3 2)::
(makeTM BR1 CL0 BL0 CL1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 BL0 CL1 DR1 CL1 HR1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 BL0 CR1 DR0 DL1 EL1 AR0 AL0 HR1,RWL 4 2)::
(makeTM BR1 CL0 BL1 AR0 DL1 DR1 CR1 ER1 HR1 BR0,RWL 5 2)::
(makeTM BR1 CL0 BL1 AL1 CR1 DL0 HR1 ER1 EL0 AR0,RWL 2 3)::
(makeTM BR1 CL0 BL1 AL1 CR1 DL0 EL0 DR1 HR1 AR0,RWL 2 3)::
(makeTM BR1 CL0 BL1 AL1 CR1 DR0 ER0 BR0 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL0 BL1 AL1 CR1 DR0 ER0 BR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL0 BL1 AL1 CR1 DR0 ER1 BR0 HR1 BL1,RWL 2 3)::
(makeTM BR1 CL0 BL1 AL1 CR1 DR0 ER1 BR1 HR1 BL1,RWL 2 3)::
(makeTM BR1 CL0 BL1 AL1 CR1 DR0 ER1 BR1 HR1 DL0,RWL 2 3)::
(makeTM BR1 CL0 BL1 AL1 CR1 DL1 HR1 ER0 AR0 EL0,RWL 2 3)::
(makeTM BR1 CL0 BL1 AL1 DR1 CL1 ER0 ER1 HR1 BR0,RWL 1 4)::
(makeTM BR1 CL0 BL1 AR1 HR1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL0 BL1 AR1 HR1 DL1 ER0 AL0 BR0 ER1,RWL 6 2)::
(makeTM BR1 CL0 BL1 AR1 HR1 DL1 ER0 DL0 ER1 AL1,RWL 2 2)::
(makeTM BR1 CL0 BL1 AR1 HR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 BL1 AR1 HR1 DR1 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 BL1 AR1 DR0 CL1 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 BL1 CL0 CR1 DR0 AL0 ER1 HR1 DR1,RWL 2 3)::
(makeTM BR1 CL0 BL1 CR1 HR1 DR0 ER0 DL1 EL1 AL0,RWL 3 2)::
(makeTM BR1 CL0 BL1 CR1 AR1 DL1 ER1 AL1 HR1 DR0,RWL 3 2)::
(makeTM BR1 CL0 CL0 HR1 HR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL0 HR1 ER1 DL1 ER1 AR1 AL1 DR0,RWL 9 2)::
(makeTM BR1 CL0 CL0 AR1 HR1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL0 CL0 AR1 HR1 DL1 ER0 DL0 ER1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 AR1 DR0 CL1 EL0 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 BL0 CR1 DR1 AL1 ER1 HR1 BL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 BL0 CR1 DR1 AL1 ER1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CL0 CL0 BR1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 BR1 DR1 CL1 HR1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 CL0 CL1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 CL1 DR1 CL1 HR1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 CL0 CR1 HR1 DR0 EL1 DL0 AL1 CR0,RWL 2 3)::
(makeTM BR1 CL0 CL0 CR1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 DL0 HR1 AL1 ER0 DL1 AR1 ER1,RWL 2 2)::
(makeTM BR1 CL0 CL0 DR0 HR1 AL1 ER1 AL0 CL1 DR1,RWL 2 3)::
(makeTM BR1 CL0 CL0 DR0 EL1 AL1 AR1 AL1 HR1 DL1,RWL 6 2)::
(makeTM BR1 CL0 CL0 DL1 HR1 AL1 EL0 DL0 ER1 AR1,RWL 2 2)::
(makeTM BR1 CL0 CL0 DL1 HR1 AL1 ER0 DL0 ER1 AR1,RWL 2 2)::
(makeTM BR1 CL0 CL0 DL1 HR1 AL1 ER0 DL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 CL0 CL0 DL1 CR1 DR0 AL1 ER1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 DL1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 DR1 HR1 DR1 BL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL0 DR1 AL1 BL0 ER1 HR1 BR0 CR0,RWL 3 2)::
(makeTM BR1 CL0 CL0 DR1 AL1 DL1 BL1 ER0 HR1 CR1,RWL 5 3)::
(makeTM BR1 CL0 CL0 DR1 DR0 CL1 EL1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL0 DR1 ER1 AL1 CL1 ER0 AR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 CL0 DR1 ER1 AL1 CL1 ER1 AR0 HR1,RWL 4 3)::
(makeTM BR1 CL0 CL0 ER0 HR1 DR0 AL1 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL0 ER0 HR1 DL1 BR1 EL1 AR1 AL1,RWL 6 2)::
(makeTM BR1 CL0 CL0 ER0 HR1 DL1 ER0 EL1 AR1 AL1,RWL 6 2)::
(makeTM BR1 CL0 CL0 ER0 HR1 DR1 DL1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL0 ER0 DL0 DR1 AL1 AR0 CR0 HR1,RWL 2 3)::
(makeTM BR1 CL0 CL0 ER0 DL1 BL1 EL1 HR1 BR0 AL1,RWL 4 3)::
(makeTM BR1 CL0 CL0 ER0 DL1 CR1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL0 ER0 DL1 CR1 AL0 AL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 CL0 CL0 ER0 DL1 DR1 AL1 AR0 HR1 CR0,RWL 3 2)::
(makeTM BR1 CL0 CL0 EL1 CR1 DR0 BL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL0 CL0 ER1 AL1 DR0 CR1 AR1 AR1 HR1,RWL 2 3)::
(makeTM BR1 CL0 CL0 ER1 DR0 CL1 AL1 DR1 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL0 CR0 HR1 CL1 DR1 EL0 DL0 ER1 AR0,RWL 1 4)::
(makeTM BR1 CL0 CR0 HR1 DR0 CR1 EL1 ER0 AL0 BR1,RWL 20 2)::
(makeTM BR1 CL0 CR0 HR1 DR0 EL1 DL1 AL0 DL0 BL0,RWL 4 2)::
(makeTM BR1 CL0 CR0 HR1 DR1 AL0 ER1 AR1 EL0 AL1,RWL 5 2)::
(makeTM BR1 CL0 CR0 AR0 DL1 DL0 AL1 ER0 HR1 AR1,RWL 4 3)::
(makeTM BR1 CL0 CR0 AR0 DL1 EL0 AL1 DL0 DR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 CR0 AR0 DL1 EL1 AL1 DL0 BR1 HR1,RWL 4 2)::
(makeTM BR1 CL0 CR0 AR0 DR1 AL1 EL0 HR1 AR1 EL1,RWL 44 2)::
(makeTM BR1 CL0 CR0 AR1 DL0 ER1 AL1 DR1 DR0 HR1,RWL 5 2)::
(makeTM BR1 CL0 CR0 AR1 DR0 AL1 ER0 HR1 EL1 AR1,RWL 2 2)::
(makeTM BR1 CL0 CR0 AR1 DL1 BR0 EL1 HR1 BL0 AL1,RWL 6 2)::
(makeTM BR1 CL0 CR0 BL0 DR1 AL1 ER1 HR1 CL1 AR0,RWL 4 2)::
(makeTM BR1 CL0 CR0 BR0 DL0 AL1 CL1 ER1 DR1 HR1,RWL 4 2)::
(makeTM BR1 CL0 CR0 BR0 DL0 EL0 EL1 HR1 AR1 CL1,RWL 2 2)::
(makeTM BR1 CL0 CR0 BR0 DL1 EL0 AL0 HR1 AR1 CL1,RWL 4 3)::
(makeTM BR1 CL0 CR0 BR0 DL1 EL0 AL0 AL1 AR0 HR1,RWL 12 2)::
(makeTM BR1 CL0 CR0 BR0 DL1 EL0 AL0 DL1 AR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR0 BR0 DR1 EL1 ER1 HR1 CL0 AR1,RWL 5 2)::
(makeTM BR1 CL0 CR0 BR1 DL0 ER0 AL1 HR1 DL1 BR0,RWL 2 2)::
(makeTM BR1 CL0 CR0 BR1 DL1 BR0 AL0 EL0 AR1 HR1,RWL 8 2)::
(makeTM BR1 CL0 CR0 BR1 DL1 BR0 AL0 EL1 AL1 HR1,RWL 9 2)::
(makeTM BR1 CL0 CR0 BR1 DL1 BR0 AL0 EL1 BR1 HR1,RWL 8 2)::
(makeTM BR1 CL0 CR0 CR1 DL1 BR1 EL0 AL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 CL0 CR0 DL0 DR1 CR1 EL1 BR0 HR1 AL0,RWL 6 3)::
(makeTM BR1 CL0 CR0 DR0 AL1 AL0 CR1 ER1 BR0 HR1,RWL 19 2)::
(makeTM BR1 CL0 CR0 DR0 AL1 EL0 CR1 HR1 BL0 AR0,RWL 3 3)::
(makeTM BR1 CL0 CR0 DR0 AL1 EL0 ER1 HR1 CR1 ER0,RWL 2 3)::
(makeTM BR1 CL0 CR0 DR0 DL1 BR0 AL0 EL0 AR1 HR1,RWL 8 2)::
(makeTM BR1 CL0 CR0 DR0 DL1 BR0 AL0 EL1 BR1 HR1,RWL 8 2)::
(makeTM BR1 CL0 CR0 DL1 DL1 ER1 AL0 DR0 AR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR0 DR1 AL1 EL0 CR1 HR1 BL0 DR0,RWL 5 3)::
(makeTM BR1 CL0 CR0 DR1 AL1 EL0 CR1 HR1 ER1 DR0,RWL 14 2)::
(makeTM BR1 CL0 CR0 DR1 AL1 EL1 CR1 HR1 DL0 ER0,RWL 5 3)::
(makeTM BR1 CL0 CR0 DR1 AL1 EL1 ER0 HR1 CR1 AR0,RWL 8 2)::
(makeTM BR1 CL0 CR0 DR1 CL1 DL1 AL1 ER1 HR1 BR0,RWL 3 3)::
(makeTM BR1 CL0 CR0 ER0 DR0 CR1 EL1 AR1 AL0 HR1,RWL 10 2)::
(makeTM BR1 CL0 CR0 ER0 DL1 BR0 EL0 HR1 CR0 AL1,RWL 7 2)::
(makeTM BR1 CL0 CR0 ER0 DR1 AL1 AL1 HR1 BR0 AR1,RWL 9 2)::
(makeTM BR1 CL0 CL1 HR1 HR1 DR1 ER0 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL1 HR1 DR0 CL1 EL1 DR1 CL1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL1 HR1 DR0 CL1 EL1 DR1 CR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL1 HR1 DR0 CL1 EL1 DR1 DR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CL1 HR1 DR1 CL1 CL1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 CL1 HR1 DR1 CL1 CR1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 CL1 HR1 DR1 DL0 ER0 EL0 CL0 AR1,RWL 2 3)::
(makeTM BR1 CL0 CL1 AL0 DR1 BL0 BR1 ER0 CR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 CL1 AL0 DR1 CR1 BL1 ER1 HR1 CR0,RWL 6 2)::
(makeTM BR1 CL0 CL1 AR0 AL1 DR0 EL1 DL1 BL1 HR1,RWL 6 2)::
(makeTM BR1 CL0 CL1 AR0 AL1 DL1 EL1 HR1 BL1 EL1,RWL 4 4)::
(makeTM BR1 CL0 CL1 AR0 BR0 DL0 EL0 HR1 AL1 ER1,RWL 4 2)::
(makeTM BR1 CL0 CL1 AR0 DL1 DL0 AL1 ER1 HR1 BR0,RWL 3 3)::
(makeTM BR1 CL0 CL1 AR0 EL0 DR1 HR1 BR0 AL1 BR0,RWL 5 3)::
(makeTM BR1 CL0 CL1 AR1 HR1 DR1 ER0 BL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL1 AR1 AL1 DL0 BR0 ER0 DR1 HR1,RWL 8 2)::
(makeTM BR1 CL0 CL1 AR1 AL1 DR0 BL0 ER1 BR0 HR1,RWL 8 2)::
(makeTM BR1 CL0 CL1 AR1 EL0 DL1 DR1 BR0 HR1 AL0,RWL 4 2)::
(makeTM BR1 CL0 CL1 BR0 AR0 DL0 EL1 HR1 AL1 CR0,RWL 4 2)::
(makeTM BR1 CL0 CL1 BR0 EL1 DL1 EL1 HR1 ER1 AR0,RWL 3 3)::
(makeTM BR1 CL0 CL1 BL1 AR1 DR1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 CL0 CL1 BL1 ER0 DR1 AR1 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 CL0 CL1 CL1 DR1 BR0 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL1 CR1 HR1 DR0 EL1 DL0 AL1 CR0,RWL 2 3)::
(makeTM BR1 CL0 CL1 CR1 AR0 DL1 BL1 EL0 HR1 AL1,RWL 4 2)::
(makeTM BR1 CL0 CL1 CR1 AR1 DL1 ER1 AL1 HR1 DR0,RWL 3 2)::
(makeTM BR1 CL0 CL1 DL0 HR1 BR1 ER0 DR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL1 DL0 DR0 BL0 AL1 ER1 AR0 HR1,RWL 2 2)::
(makeTM BR1 CL0 CL1 DR0 HR1 BR1 ER1 AL0 EL1 DL0,RWL 2 3)::
(makeTM BR1 CL0 CL1 DR0 HR1 DR0 ER1 AL1 EL1 DL0,RWL 2 3)::
(makeTM BR1 CL0 CL1 DR0 AL1 BL1 ER0 CR1 HR1 CL1,RWL 14 2)::
(makeTM BR1 CL0 CL1 DR0 AL1 CL1 DL1 ER0 HR1 CR1,RWL 2 3)::
(makeTM BR1 CL0 CL1 DR0 BR1 CL1 HR1 ER1 AL1 DR1,RWL 2 3)::
(makeTM BR1 CL0 CL1 DR0 BR1 CL1 HR1 ER1 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 CL1 DL1 DL0 BL1 ER1 AR0 CR1 HR1,RWL 4 2)::
(makeTM BR1 CL0 CL1 DR1 HR1 DR1 ER0 BL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL1 DR1 AL0 DL1 ER0 BL0 HR1 AR1,RWL 4 2)::
(makeTM BR1 CL0 CL1 DR1 AL1 BR0 CR1 ER0 HR1 DL1,RWL 6 3)::
(makeTM BR1 CL0 CL1 DR1 AL1 BR0 CR1 ER1 HR1 BR0,RWL 6 3)::
(makeTM BR1 CL0 CL1 DR1 AL1 CL0 ER0 HR1 AR0 ER1,RWL 8 3)::
(makeTM BR1 CL0 CL1 DR1 AL1 DL1 BL1 ER0 HR1 CR1,RWL 29 2)::
(makeTM BR1 CL0 CL1 ER0 HR1 DL0 AR0 AR1 EL1 AL0,RWL 2 3)::
(makeTM BR1 CL0 CL1 ER0 HR1 DL0 AR0 BR1 EL1 AL1,RWL 3 3)::
(makeTM BR1 CL0 CL1 ER0 HR1 DR0 AL0 AL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL1 ER0 HR1 DR0 AL1 AL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL0 CL1 ER0 HR1 DL1 DR0 EL0 AL1 AR1,RWL 4 2)::
(makeTM BR1 CL0 CL1 ER0 AR0 DL0 AR1 CL0 DR1 HR1,RWL 4 3)::
(makeTM BR1 CL0 CL1 ER0 AL1 DL0 CR1 DR0 DR1 HR1,RWL 2 3)::
(makeTM BR1 CL0 CL1 ER0 AR1 DL1 AL1 AL0 HR1 AR1,RWL 9 2)::
(makeTM BR1 CL0 CL1 ER0 DR0 CL1 HR1 BR1 EL1 AL1,RWL 3 2)::
(makeTM BR1 CL0 CL1 ER0 DR0 DL1 AL1 HR1 BL0 AR0,RWL 4 2)::
(makeTM BR1 CL0 CL1 EL1 DR1 BL0 HR1 AR1 AL0 ER0,RWL 20 2)::
(makeTM BR1 CL0 CL1 EL1 DR1 BL0 AR0 DR1 HR1 CL1,RWL 6 2)::
(makeTM BR1 CL0 CL1 ER1 AL1 DL0 DR1 ER0 CR1 HR1,RWL 14 2)::
(makeTM BR1 CL0 CL1 ER1 AL1 DL0 EL0 HR1 BR0 AR0,RWL 57 2)::
(makeTM BR1 CL0 CR1 HR1 AL1 DL0 DR1 ER0 AL0 ER1,RWL 1 3)::
(makeTM BR1 CL0 CR1 HR1 DR0 CL1 EL1 DR1 CL1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CR1 HR1 DR0 CL1 EL1 DR1 CR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CR1 HR1 DR0 CL1 EL1 DR1 DR1 AL1,RWL 2 2)::
(makeTM BR1 CL0 CR1 HR1 DL1 ER0 AL0 AR1 CL1 DR0,RWL 7 2)::
(makeTM BR1 CL0 CR1 HR1 DL1 ER0 BL0 AL0 AL0 DR0,RWL 14 2)::
(makeTM BR1 CL0 CR1 HR1 DL1 ER1 EL0 DL1 BR0 AL0,RWL 4 3)::
(makeTM BR1 CL0 CR1 HR1 DR1 CL1 CL1 ER0 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL0 CR1 HR1 DR1 DL0 EL1 BR0 CR1 AL0,RWL 4 3)::
(makeTM BR1 CL0 CR1 AL0 DR0 DL1 EL1 BR0 BL1 HR1,RWL 7 2)::
(makeTM BR1 CL0 CR1 AL0 DL1 BR0 HR1 EL1 BL1 EL1,RWL 3 2)::
(makeTM BR1 CL0 CR1 AL0 DL1 BR0 HR1 EL1 BL1 ER1,RWL 3 2)::
(makeTM BR1 CL0 CR1 AL0 DL1 BR0 HR1 ER1 BL1 EL1,RWL 3 2)::
(makeTM BR1 CL0 CR1 AL0 DL1 CR0 BR0 EL0 HR1 BL1,RWL 3 3)::
(makeTM BR1 CL0 CR1 AL0 DR1 CR1 BL1 ER1 HR1 CR0,RWL 6 2)::
(makeTM BR1 CL0 CR1 AL0 DR1 DL0 BL1 ER0 CR1 HR1,RWL 4 3)::
(makeTM BR1 CL0 CR1 AL0 DR1 DL1 EL1 BR0 HR1 BL1,RWL 2 2)::
(makeTM BR1 CL0 CR1 AR0 AL1 DL0 BL0 ER0 DR0 HR1,RWL 8 2)::
(makeTM BR1 CL0 CR1 AR0 DL1 BL0 HR1 EL0 AR1 EL1,RWL 4 3)::
(makeTM BR1 CL0 CR1 AR0 DL1 BR1 HR1 EL0 AL0 EL1,RWL 24 2)::
(makeTM BR1 CL0 CR1 AR1 AL1 DL0 DR1 ER0 CR1 HR1,RWL 3 3)::
(makeTM BR1 CL0 CR1 AR1 DL0 EL0 AL1 DL1 HR1 AR0,RWL 4 4)::
(makeTM BR1 CL0 CR1 AR1 DL1 AR0 HR1 EL0 AL0 EL1,RWL 11 2)::
(makeTM BR1 CL0 CR1 AR1 DL1 EL0 AL1 DL0 HR1 AR0,RWL 4 3)::
(makeTM BR1 CL0 CR1 BL0 DR1 EL1 ER1 HR1 AL1 AR0,RWL 1 3)::
(makeTM BR1 CL0 CR1 BR0 AL1 DL0 ER0 EL0 CR0 HR1,RWL 2 3)::
(makeTM BR1 CL0 CR1 BR0 AL1 DL1 AR0 ER1 HR1 DR0,RWL 6 2)::
(makeTM BR1 CL0 CR1 BR0 DL1 EL0 HR1 BL0 AL1 EL1,RWL 1 4)::
(makeTM BR1 CL0 CR1 BR0 DL1 EL0 AL1 DL0 HR1 DR0,RWL 12 2)::
(makeTM BR1 CL0 CR1 BL1 DL1 BR0 AL1 ER0 HR1 DR1,RWL 1 3)::
(makeTM BR1 CL0 CR1 BR1 AL1 DL0 DR1 ER0 CR1 HR1,RWL 14 2)::
(makeTM BR1 CL0 CR1 BR1 AL1 DR0 CL1 ER0 HR1 AR0,RWL 4 4)::
(makeTM BR1 CL0 CR1 BR1 AL1 DL1 EL1 DR0 CL1 HR1,RWL 3 2)::
(makeTM BR1 CL0 CR1 BR1 AL1 DR1 ER0 BL1 HR1 CR1,RWL 1 3)::
(makeTM BR1 CL0 CR1 BR1 DL0 BR0 HR1 EL1 AL1 BL0,RWL 11 2)::
(makeTM BR1 CL0 CR1 CL0 DL1 ER0 AL1 AR1 DR1 HR1,RWL 5 2)::
(makeTM BR1 CL0 CR1 CL1 AL1 DR1 ER0 BR1 HR1 CR1,RWL 1 3)::
(makeTM BR1 CL0 CR1 DL0 AL1 BR0 ER1 DR1 AR1 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 DL0 BL1 ER0 HR1 EL1 AL0 AR1,RWL 5 2)::
(makeTM BR1 CL0 CR1 DL0 DR1 CR0 BL1 EL1 HR1 AL0,RWL 7 2)::
(makeTM BR1 CL0 CR1 DL0 DR1 ER1 BL1 CR0 AR1 HR1,RWL 4 4)::
(makeTM BR1 CL0 CR1 DR0 DL1 ER1 HR1 CR1 EL1 AL1,RWL 2 3)::
(makeTM BR1 CL0 CR1 DR1 AL1 BL0 ER1 HR1 AR0 BR0,RWL 4 2)::
(makeTM BR1 CL0 CR1 DR1 AL1 BR0 EL0 HR1 AR0 EL0,RWL 2 3)::
(makeTM BR1 CL0 CR1 DR1 AL1 BR0 ER1 AR1 HR1 CR0,RWL 6 2)::
(makeTM BR1 CL0 CR1 DR1 AL1 BL1 ER1 BR0 HR1 AR0,RWL 4 2)::
(makeTM BR1 CL0 CR1 DR1 AL1 BL1 ER1 BR0 HR1 AR1,RWL 4 2)::
(makeTM BR1 CL0 CR1 DR1 DL0 ER0 BL1 AL1 AR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 DR1 DR0 HR1 EL1 AR0 DL0 BL0,RWL 3 2)::
(makeTM BR1 CL0 CR1 DR1 DL1 EL0 AL1 BR0 HR1 CR0,RWL 16 2)::
(makeTM BR1 CL0 CR1 DR1 DL1 EL1 AL1 BR0 HR1 AL1,RWL 16 2)::
(makeTM BR1 CL0 CR1 EL0 AL1 DL0 DR1 BR0 HR1 AR1,RWL 14 2)::
(makeTM BR1 CL0 CR1 EL0 AL1 DL1 BL0 DR0 HR1 AR1,RWL 5 3)::
(makeTM BR1 CL0 CR1 EL0 DL1 AR0 HR1 EL1 AL1 BL1,RWL 4 3)::
(makeTM BR1 CL0 CR1 EL0 DR1 BR0 DL1 AL0 AL1 HR1,RWL 2 3)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL0 BL0 AR0 AL0 HR1,RWL 10 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL0 CR1 AL0 AR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL0 DR1 BR0 AL0 HR1,RWL 14 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DR0 ER1 HR1 AR1 AL0,RWL 8 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL1 AL0 DR0 BL1 HR1,RWL 3 3)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL1 AL0 DR0 DR0 HR1,RWL 3 3)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL1 AR0 DR0 DR1 HR1,RWL 9 4)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL1 BL0 DR0 AL0 HR1,RWL 5 3)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL1 CL0 AL0 AR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL1 CL0 BR1 AR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL1 EL1 AL0 AR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL1 EL1 BR1 AR0 HR1,RWL 4 2)::
(makeTM BR1 CL0 CR1 ER0 DL0 AR0 BR0 CL1 AR1 HR1,RWL 3 2)::
(makeTM BR1 CL0 CR1 ER0 DL0 BR0 AL1 DR1 BR1 HR1,RWL 8 2)::
(makeTM BR1 CL0 CR1 ER0 DR0 BL0 AL1 HR1 DL1 AR1,RWL 5 3)::
(makeTM BR1 CL0 CR1 ER0 DL1 CR0 AL1 AR0 HR1 BR1,RWL 4 2)::
(makeTM BR1 CL0 CR1 ER0 DL1 DR0 BR1 AL0 CL1 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 ER0 DL1 DR1 BL0 AL0 BR1 HR1,RWL 3 2)::
(makeTM BR1 CL0 CR1 ER0 DR1 AL1 CL1 HR1 ER1 AR0,RWL 2 2)::
(makeTM BR1 CL0 CR1 ER0 DR1 AL1 EL1 HR1 AR1 EL1,RWL 12 2)::
(makeTM BR1 CL0 CR1 ER0 DR1 EL1 ER1 HR1 AL1 AR0,RWL 1 4)::
(makeTM BR1 CL0 CR1 EL1 DL1 AR0 HR1 EL0 BL1 ER0,RWL 9 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL0 AL1 AL1 BR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL0 BL0 AR0 CR1 HR1,RWL 10 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL0 BL0 AR0 DR0 HR1,RWL 12 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL0 DR1 AL1 BR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL0 DR1 BR0 CR1 HR1,RWL 14 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL0 DR1 ER0 CR1 HR1,RWL 14 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL0 ER0 AL1 BR0 HR1,RWL 2 3)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL1 AL0 DR0 AR1 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL1 AL0 DR0 DL1 HR1,RWL 3 3)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL1 AR0 AR0 BR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL1 AR0 CR0 BR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL1 CR1 AR0 BR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 ER1 AL1 DL1 CR1 AR0 DR0 HR1,RWL 6 2)::
(makeTM BR1 CL0 CR1 ER1 DL1 CR0 AL1 AR0 HR1 DL0,RWL 4 2)::
(makeTM BR1 CR0 AL0 HR1 DL1 CR1 CR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 AL0 CR1 DL1 AL0 EL0 HR1 ER1 BR0,RWL 2 2)::
(makeTM BR1 CR0 AL0 CR1 DL1 EL0 AL1 HR1 BR0 AR1,RWL 2 2)::
(makeTM BR1 CR0 AL0 CR1 DL1 EL0 EL0 HR1 ER1 BR0,RWL 2 2)::
(makeTM BR1 CR0 AL0 DR1 DL1 ER0 AL1 BR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 CR0 AL0 ER1 DL1 CR1 AL1 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR0 AL0 ER1 DL1 DR0 AL1 BL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR0 AL1 HR1 BL0 DL1 DR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CR0 AL1 AR0 ER1 DL0 EL1 HR1 CL1 BL0,RWL 6 3)::
(makeTM BR1 CR0 AL1 AR1 AR1 DL1 CL0 EL0 HR1 CR0,RWL 6 2)::
(makeTM BR1 CR0 AL1 AR1 AR1 DL1 CL0 EL1 HR1 BR0,RWL 6 2)::
(makeTM BR1 CR0 AL1 CR0 AL1 DR1 EL1 ER0 HR1 CL0,RWL 2 3)::
(makeTM BR1 CR0 AL1 CR0 CL1 DL0 BR0 EL1 HR1 DL1,RWL 2 3)::
(makeTM BR1 CR0 AL1 CL1 DL1 CR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 AL1 CR1 HR1 DL1 EL0 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 CR0 AL1 CR1 DL1 CR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 AL1 DL0 DL1 CR1 EL0 AR1 HR1 BL0,RWL 2 3)::
(makeTM BR1 CR0 AL1 DL0 ER0 BL1 CR1 DL1 HR1 AR0,RWL 2 3)::
(makeTM BR1 CR0 AL1 DR0 AR1 DL1 CL0 EL0 HR1 CR0,RWL 6 2)::
(makeTM BR1 CR0 AL1 DR0 BL0 BL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CR0 AL1 DR1 BL0 BL1 HR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR1 CR0 AL1 DR1 CR1 BR0 DL1 EL0 HR1 CL0,RWL 3 2)::
(makeTM BR1 CR0 AL1 ER0 AR1 DL1 CL0 AL0 CL0 HR1,RWL 6 2)::
(makeTM BR1 CR0 AL1 ER0 DR1 DL0 CL1 BL0 AR1 HR1,RWL 6 3)::
(makeTM BR1 CR0 AL1 EL1 CL1 DL0 BR0 EL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 CR0 AL1 ER1 AR1 DL1 CL0 AL0 BR1 HR1,RWL 6 2)::
(makeTM BR1 CR0 AL1 ER1 DL0 CR1 AL1 DL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 CR0 AL1 ER1 DL1 CR1 HR1 BL0 EL0 AR1,RWL 1 4)::
(makeTM BR1 CR0 BL0 CR1 CL1 DL0 EL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 BL0 CR1 DL0 CR1 ER1 DL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 CR0 BL0 CR1 DL1 BR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 BL0 CR1 DL1 CR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 BL1 AL1 HR1 DL0 EL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 BL1 AL1 DL0 CL1 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CR0 BL1 AR1 DL1 BR0 EL0 HR1 BR1 CL0,RWL 13 2)::
(makeTM BR1 CR0 BL1 AR1 DL1 BR0 EL0 HR1 ER1 CL0,RWL 13 2)::
(makeTM BR1 CR0 BL1 AR1 DL1 CR1 AL0 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 CR0 BL1 CL0 DR1 DL1 AR1 ER0 HR1 BR0,RWL 3 2)::
(makeTM BR1 CR0 BL1 CL0 DR1 EL0 AR1 HR1 AL0 AR1,RWL 5 2)::
(makeTM BR1 CR0 BL1 CR0 AL1 DR1 EL1 ER0 HR1 CL0,RWL 2 3)::
(makeTM BR1 CR0 BL1 CR1 HR1 DR0 DL1 EL1 AL1 CL0,RWL 3 2)::
(makeTM BR1 CR0 CL0 HR1 DL0 CR1 ER1 DL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 CR0 CL0 HR1 ER1 DL1 AR1 CL1 DR0 CL0,RWL 4 3)::
(makeTM BR1 CR0 CL0 AR0 HR1 DL0 EL1 DL1 BR1 ER1,RWL 3 2)::
(makeTM BR1 CR0 CL0 AR0 AL1 DL1 EL1 HR1 BL0 CL1,RWL 6 2)::
(makeTM BR1 CR0 CL0 AR0 DL1 CR1 DL0 EL0 AL1 HR1,RWL 2 3)::
(makeTM BR1 CR0 CL0 AR0 EL1 DL0 BR0 HR1 BR1 CL1,RWL 35 2)::
(makeTM BR1 CR0 CL0 AR0 EL1 DL0 EL1 HR1 BR1 CL1,RWL 35 2)::
(makeTM BR1 CR0 CL0 AR0 ER1 DL1 EL0 HR1 AL1 BR0,RWL 2 2)::
(makeTM BR1 CR0 CL0 AR1 HR1 DR1 EL0 DR1 BR1 EL1,RWL 2 2)::
(makeTM BR1 CR0 CL0 AR1 DL0 CR1 HR1 EL1 BR1 EL1,RWL 2 2)::
(makeTM BR1 CR0 CL0 AR1 DL0 CR1 ER0 DL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CR0 CL0 AR1 DL0 CR1 ER1 DL1 HR1 BL0,RWL 3 2)::
(makeTM BR1 CR0 CL0 AR1 DL0 CR1 ER1 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 CR0 CL0 AR1 EL1 DL1 BR0 AL0 CL1 HR1,RWL 2 3)::
(makeTM BR1 CR0 CL0 AR1 EL1 DL1 BR0 BL1 AL0 HR1,RWL 6 3)::
(makeTM BR1 CR0 CL0 BL0 DR0 BL1 ER1 HR1 AR1 CR1,RWL 3 2)::
(makeTM BR1 CR0 CL0 BL0 DR1 BL1 DL0 ER1 AR0 HR1,RWL 4 3)::
(makeTM BR1 CR0 CL0 BR0 CL1 DL1 AR1 EL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR0 CL0 BR0 CL1 DL1 EL0 HR1 ER1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CL0 BR0 ER0 DL0 BL0 DL1 AR1 HR1,RWL 7 2)::
(makeTM BR1 CR0 CL0 BR1 HR1 DL1 EL0 DL1 ER1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CL0 BR1 DL1 CR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CL0 CR0 AL1 DR0 BL1 ER0 HR1 AL0,RWL 2 3)::
(makeTM BR1 CR0 CL0 CR0 AL1 DR0 BL1 ER0 HR1 BL1,RWL 2 3)::
(makeTM BR1 CR0 CL0 CR0 AL1 DR0 BL1 ER1 HR1 CL0,RWL 2 3)::
(makeTM BR1 CR0 CL0 CR0 AL1 DR1 EL1 ER0 HR1 CL0,RWL 2 3)::
(makeTM BR1 CR0 CL0 CL1 HR1 DL1 CR1 EL0 ER1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CL0 CL1 DL1 CR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CL0 CL1 DR1 BL1 ER0 AR0 HR1 CL1,RWL 2 3)::
(makeTM BR1 CR0 CL0 CL1 DR1 BL1 ER1 AR0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CL0 CR1 DL1 CR1 HR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CL0 DR0 DL1 CL1 ER0 CL0 HR1 AR1,RWL 4 2)::
(makeTM BR1 CR0 CL0 DR1 AR1 DL1 ER1 AL0 HR1 AR1,RWL 4 2)::
(makeTM BR1 CR0 CL0 DR1 AR1 DL1 ER1 AL0 HR1 BR0,RWL 4 2)::
(makeTM BR1 CR0 CL0 ER0 DL1 BL1 EL1 HR1 BR0 AL1,RWL 4 3)::
(makeTM BR1 CR0 CL0 ER0 DL1 CL1 AL1 CL0 HR1 AR0,RWL 6 2)::
(makeTM BR1 CR0 CL0 ER0 DL1 DL0 AL1 EL1 AR1 HR1,RWL 1 4)::
(makeTM BR1 CR0 CL0 ER0 ER1 DL1 EL0 HR1 BL1 AR0,RWL 16 2)::
(makeTM BR1 CR0 CL0 EL1 DL1 CR1 HR1 EL0 AR1 BL1,RWL 4 3)::
(makeTM BR1 CR0 CL0 ER1 DL0 CR1 AL1 DL1 HR1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CR0 HR1 BL1 DR0 DL1 EL0 AL0 AL1,RWL 3 2)::
(makeTM BR1 CR0 CR0 HR1 CL1 DL0 ER0 AL1 DL1 AL0,RWL 2 2)::
(makeTM BR1 CR0 CR0 HR1 CL1 DL0 ER0 DL1 AL0 AR1,RWL 2 3)::
(makeTM BR1 CR0 CR0 HR1 CL1 DR1 EL0 DL0 ER1 AR0,RWL 1 4)::
(makeTM BR1 CR0 CR0 HR1 DL1 CR1 AL0 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 CR0 CR0 HR1 DL1 CR1 AL0 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CR0 HR1 DL1 CR1 EL1 EL0 AR1 AL0,RWL 2 3)::
(makeTM BR1 CR0 CR0 HR1 DL1 CR1 EL1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CR0 HR1 DL1 CR1 ER1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CR0 HR1 DR1 EL0 CL1 DR1 AL0 AL1,RWL 2 4)::
(makeTM BR1 CR0 CR0 HR1 DR1 EL0 DL1 CL0 BR1 AL1,RWL 2 3)::
(makeTM BR1 CR0 CR0 AL0 DL1 ER1 AL0 BL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 CR0 CR0 AR0 DL0 EL0 AL1 ER0 CL1 HR1,RWL 4 2)::
(makeTM BR1 CR0 CR0 BR0 CL1 DL1 AR1 EL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 CR0 CR0 BR0 CL1 DL1 AR1 EL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR0 CR0 BR0 CL1 DL1 EL0 HR1 ER1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CR0 BL1 CL0 DL1 EL0 HR1 ER1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CR0 BL1 CL1 DL1 EL0 HR1 ER1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CR0 BL1 DL1 CR1 AL0 EL1 HR1 BL0,RWL 2 3)::
(makeTM BR1 CR0 CR0 BR1 DL0 CR1 EL1 DL1 HR1 AL1,RWL 2 3)::
(makeTM BR1 CR0 CR0 DL0 BL1 CR1 AL0 EL0 HR1 AL0,RWL 2 4)::
(makeTM BR1 CR0 CR0 DL0 BL1 CR1 AL0 EL1 HR1 BR0,RWL 2 4)::
(makeTM BR1 CR0 CR0 DL0 DL1 CR1 AL0 EL1 HR1 BR0,RWL 2 3)::
(makeTM BR1 CR0 CR0 DR0 AL1 AL0 DL1 ER1 HR1 CL0,RWL 2 3)::
(makeTM BR1 CR0 CR0 DR0 AL1 EL0 DL1 CR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CR0 CR0 DR1 AL1 AL0 EL1 ER0 HR1 CL0,RWL 2 3)::
(makeTM BR1 CR0 CR0 EL1 DL1 BR0 BL0 HR1 AL0 CL1,RWL 4 2)::
(makeTM BR1 CR0 CR0 EL1 DL1 CR1 BR1 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 CR0 CR0 ER1 CL1 DL0 AL1 HR1 BL1 AR0,RWL 5 2)::
(makeTM BR1 CR0 CR0 ER1 DL0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR0 CR0 ER1 DL0 CR1 AL1 DL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 CR0 CR0 ER1 DR0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR0 CR0 ER1 DL1 CR1 AL1 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR0 CL1 HR1 AL0 DL0 ER1 DL1 CR0 AR0,RWL 2 3)::
(makeTM BR1 CR0 CL1 HR1 AL0 DL1 AR1 EL0 AR0 EL1,RWL 2 2)::
(makeTM BR1 CR0 CL1 HR1 BL0 DL0 DR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR1 CR0 CL1 HR1 DL1 CR1 CL1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CL1 HR1 DL1 CR1 CR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CL1 HR1 DR1 DL1 AR1 EL1 BR1 EL0,RWL 5 2)::
(makeTM BR1 CR0 CL1 HR1 ER1 DL1 CL0 AL0 AR0 DR1,RWL 2 3)::
(makeTM BR1 CR0 CL1 AL0 DL0 AR1 EL1 HR1 BL1 AL0,RWL 5 2)::
(makeTM BR1 CR0 CL1 AL0 DR1 BL0 CL0 ER1 AR0 HR1,RWL 6 2)::
(makeTM BR1 CR0 CL1 AR0 HR1 DL1 EL0 AR1 ER1 DL0,RWL 3 2)::
(makeTM BR1 CR0 CL1 AR0 AR0 DL1 EL1 HR1 CL0 AL0,RWL 3 2)::
(makeTM BR1 CR0 CL1 AR0 AL1 DL0 EL1 HR1 BL0 CR0,RWL 12 2)::
(makeTM BR1 CR0 CL1 AR0 AL1 DL1 EL1 HR1 BL0 CL0,RWL 4 2)::
(makeTM BR1 CR0 CL1 AR0 BL0 DL0 EL1 HR1 AL1 DL1,RWL 2 2)::
(makeTM BR1 CR0 CL1 AR0 DR1 BL0 ER1 DL0 AR1 HR1,RWL 4 2)::
(makeTM BR1 CR0 CL1 AR0 DR1 DL0 BL0 EL1 HR1 AL1,RWL 11 3)::
(makeTM BR1 CR0 CL1 AR0 DR1 DL0 BL0 ER1 AR1 HR1,RWL 1 4)::
(makeTM BR1 CR0 CL1 AR0 ER0 DL0 EL0 HR1 AL1 EL1,RWL 6 2)::
(makeTM BR1 CR0 CL1 AR0 ER1 DL0 BL0 AL1 HR1 BR0,RWL 3 4)::
(makeTM BR1 CR0 CL1 AL1 DL0 CL1 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CR0 CL1 AL1 DR1 BL0 AR1 ER0 AR1 HR1,RWL 4 3)::
(makeTM BR1 CR0 CL1 AL1 DR1 BL0 BR0 ER1 AR0 HR1,RWL 8 2)::
(makeTM BR1 CR0 CL1 AL1 DR1 BL0 BR1 ER1 DR0 HR1,RWL 6 2)::
(makeTM BR1 CR0 CL1 AR1 HR1 DL0 AR1 EL1 BR0 CR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 AR1 DL0 CR1 ER1 DL1 HR1 BL0,RWL 3 2)::
(makeTM BR1 CR0 CL1 AR1 DL0 CR1 ER1 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 CR0 CL1 AR1 EL1 DL0 DR1 BL0 BR0 HR1,RWL 2 3)::
(makeTM BR1 CR0 CL1 AR1 EL1 DL1 CL0 AL0 BR0 HR1,RWL 2 2)::
(makeTM BR1 CR0 CL1 BR0 DL0 DL1 AL1 ER0 AR0 HR1,RWL 1 4)::
(makeTM BR1 CR0 CL1 BR0 DL1 AR1 EL1 HR1 AR1 EL0,RWL 16 2)::
(makeTM BR1 CR0 CL1 BR0 DL1 DL0 AR1 EL0 HR1 BL1,RWL 7 2)::
(makeTM BR1 CR0 CL1 CL0 EL0 DR1 HR1 BL1 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 CR0 EL0 DR0 HR1 CL1 AR1 AL0,RWL 2 2)::
(makeTM BR1 CR0 CL1 CL1 HR1 DL0 AR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 CR1 AR0 DL0 EL0 HR1 ER1 BL0,RWL 3 2)::
(makeTM BR1 CR0 CL1 DL0 HR1 AL1 HR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 DL0 HR1 DL1 BR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 DL0 HR1 DL1 DR0 EL0 ER1 AR1,RWL 3 2)::
(makeTM BR1 CR0 CL1 DL0 HR1 DR1 EL0 BL1 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 DL0 AR1 BL0 AL0 ER0 DR0 HR1,RWL 8 2)::
(makeTM BR1 CR0 CL1 DL0 AR1 BL0 EL1 AL1 HR1 BL1,RWL 2 4)::
(makeTM BR1 CR0 CL1 DL0 BL1 CR1 HR1 EL1 AR1 DL1,RWL 2 3)::
(makeTM BR1 CR0 CL1 DL0 BL1 CR1 HR1 EL1 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CL1 DR0 AR0 DL0 AR1 EL0 BL0 HR1,RWL 2 2)::
(makeTM BR1 CR0 CL1 DR0 DL1 CL1 ER0 CL0 HR1 AR1,RWL 11 2)::
(makeTM BR1 CR0 CL1 DL1 HR1 BR1 EL0 DL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 DL1 AR1 AL1 EL0 BL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 CR0 CL1 DL1 AR1 AL1 EL1 BL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 CR0 CL1 DL1 BL1 DL0 AR1 EL1 HR1 BR0,RWL 2 3)::
(makeTM BR1 CR0 CL1 DL1 BR1 BL1 HR1 EL0 ER1 AL0,RWL 5 2)::
(makeTM BR1 CR0 CL1 DL1 CL1 DL0 AR1 EL1 HR1 AR1,RWL 2 3)::
(makeTM BR1 CR0 CL1 DL1 CL1 DL0 AR1 EL1 HR1 BR0,RWL 2 3)::
(makeTM BR1 CR0 CL1 DL1 DR1 AR1 BL1 ER0 HR1 BR0,RWL 2 2)::
(makeTM BR1 CR0 CL1 DR1 HR1 DL0 AR1 ER1 EL0 AL1,RWL 1 3)::
(makeTM BR1 CR0 CL1 DR1 HR1 DL0 ER1 AL1 EL0 AR1,RWL 1 4)::
(makeTM BR1 CR0 CL1 EL0 HR1 DL1 DR1 BL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 EL0 DR1 CL1 HR1 BL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR0 CL1 ER0 HR1 DL0 AR1 BR1 DR1 DL1,RWL 3 2)::
(makeTM BR1 CR0 CL1 ER0 HR1 DL0 AR1 DL1 DL0 ER1,RWL 3 2)::
(makeTM BR1 CR0 CL1 ER0 HR1 DL0 AR1 DL1 DR1 ER1,RWL 1 3)::
(makeTM BR1 CR0 CL1 ER0 AL1 DL0 BL1 DR0 HR1 DR1,RWL 8 2)::
(makeTM BR1 CR0 CL1 ER0 DL0 CL1 AL1 CL0 AR0 HR1,RWL 17 2)::
(makeTM BR1 CR0 CL1 ER0 DL1 CL1 AL1 CL0 HR1 AR0,RWL 7 2)::
(makeTM BR1 CR0 CL1 ER0 DR1 DL1 AR1 DL0 HR1 AR0,RWL 16 3)::
(makeTM BR1 CR0 CL1 EL1 HR1 DL0 AR1 ER0 BL1 DL1,RWL 2 2)::
(makeTM BR1 CR0 CL1 EL1 DR0 BL0 AR1 DL1 AL0 HR1,RWL 2 3)::
(makeTM BR1 CR0 CL1 ER1 HR1 DL0 AR1 AL1 DR1 AR1,RWL 4 2)::
(makeTM BR1 CR0 CL1 ER1 HR1 DR0 DL1 EL0 AL1 BL0,RWL 3 2)::
(makeTM BR1 CR0 CL1 ER1 DL0 CR1 BR1 DL1 HR1 AR1,RWL 3 2)::
(makeTM BR1 CR0 CL1 ER1 EL0 DR0 HR1 CL1 AR1 AL0,RWL 1 4)::
(makeTM BR1 CR0 CL1 ER1 EL0 DR1 HR1 BR0 AR1 CL1,RWL 8 2)::
(makeTM BR1 CR0 CR1 HR1 AL1 DR0 DL1 EL0 AL0 AL1,RWL 3 2)::
(makeTM BR1 CR0 CR1 HR1 AL1 DR0 DL1 ER1 AR1 EL0,RWL 5 3)::
(makeTM BR1 CR0 CR1 HR1 DL0 ER0 AL0 DL1 AL0 AR1,RWL 5 2)::
(makeTM BR1 CR0 CR1 HR1 DL0 ER0 AL0 DL1 EL1 AR1,RWL 3 3)::
(makeTM BR1 CR0 CR1 HR1 DL1 CR1 CL1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CR1 HR1 DL1 CR1 CR1 EL0 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CR1 AL0 DL0 CL1 AR1 EL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 CR0 CR1 AL0 DL0 CL1 AR1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 CR0 CR1 AL0 DL1 AL1 BR0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 CR0 CR1 AL0 DR1 DL1 EL1 BL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 CR0 CR1 AR0 DL1 DL0 AL1 EL1 HR1 DL1,RWL 6 3)::
(makeTM BR1 CR0 CR1 AL1 DL1 AL0 BR0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 CR0 CR1 AL1 DL1 AL0 BR1 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 CR0 CR1 AR1 DL0 CR1 ER1 DL1 HR1 BL0,RWL 3 2)::
(makeTM BR1 CR0 CR1 AR1 DL0 CR1 ER1 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 CR0 CR1 BL0 DL1 AR1 HR1 EL0 ER1 AL1,RWL 1 4)::
(makeTM BR1 CR0 CR1 BL0 DL1 ER1 BR1 AL0 DR0 HR1,RWL 4 2)::
(makeTM BR1 CR0 CR1 BL0 DR1 AR1 EL1 DL0 HR1 AL1,RWL 5 2)::
(makeTM BR1 CR0 CR1 BL1 BL0 DR1 HR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR1 CR0 CR1 BL1 DL0 AR1 EL1 BL0 HR1 CL0,RWL 4 2)::
(makeTM BR1 CR0 CR1 BL1 DL1 AR1 EL0 AL1 HR1 BL0,RWL 2 3)::
(makeTM BR1 CR0 CR1 BL1 DL1 AR1 EL0 CL0 HR1 CL0,RWL 4 4)::
(makeTM BR1 CR0 CR1 BL1 DR1 AR1 EL1 HR1 AL1 EL0,RWL 4 3)::
(makeTM BR1 CR0 CR1 BR1 DL1 CL1 AL1 EL0 HR1 AL1,RWL 3 2)::
(makeTM BR1 CR0 CR1 CL0 AL1 DR1 EL1 ER0 HR1 AL0,RWL 3 2)::
(makeTM BR1 CR0 CR1 DL0 BL1 AR0 ER0 CL0 DR1 HR1,RWL 3 2)::
(makeTM BR1 CR0 CR1 DL0 BL1 CR1 HR1 EL1 AR1 DL1,RWL 2 3)::
(makeTM BR1 CR0 CR1 DL0 BL1 CR1 HR1 EL1 AR1 EL1,RWL 2 3)::
(makeTM BR1 CR0 CR1 DR0 AL1 DL1 EL1 AL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 CR0 CR1 DR0 DL1 AL1 ER0 AL0 HR1 BL0,RWL 2 2)::
(makeTM BR1 CR0 CR1 DR1 BL0 ER0 BL1 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CR0 CR1 EL0 DR1 BR1 EL1 DL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CR0 CR1 ER0 DL1 CL1 AL1 CL0 HR1 AR0,RWL 8 2)::
(makeTM BR1 CR0 CR1 EL1 AL1 DR1 AL0 ER0 HR1 AL0,RWL 3 2)::
(makeTM BR1 CR0 CR1 EL1 DL1 BR1 AL0 AR1 HR1 BL0,RWL 2 3)::
(makeTM BR1 CR0 CR1 EL1 DR1 AL0 EL1 CL0 HR1 BL1,RWL 2 3)::
(makeTM BR1 CR0 CR1 ER1 DL0 CR1 BR1 DL1 HR1 AR1,RWL 3 2)::
(makeTM BR1 CL1 AL0 HR1 DR1 EL1 DL1 ER0 DR0 BL1,RWL 4 3)::
(makeTM BR1 CL1 AL0 BL1 DR1 ER0 BL0 CR1 HR1 DR1,RWL 6 4)::
(makeTM BR1 CL1 AL0 DR0 AR1 CL0 ER0 HR1 EL0 AR0,RWL 15 2)::
(makeTM BR1 CL1 AL0 DR1 DL0 EL1 AR1 AR0 HR1 BL0,RWL 35 2)::
(makeTM BR1 CL1 AL0 ER0 DR1 AL1 AR1 DL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 CL1 AL0 ER1 DL1 HR1 ER1 DL0 AR0 DR0,RWL 6 2)::
(makeTM BR1 CL1 AL1 HR1 CR1 DR0 HR1 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 CL1 AL1 HR1 DL1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL1 AL1 HR1 DR1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL1 AL1 HR1 DR1 EL0 AL1 DR1 DR0 EL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 HR1 DR1 ER1 EL1 CR0 AR1 AL0,RWL 5 2)::
(makeTM BR1 CL1 AL1 BR1 AL1 DL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 CL1 AL1 BR1 BL1 DL0 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 BL1 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 BR1 DL0 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 BR1 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 CR1 DL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 CL1 AL1 BR1 DL0 EL0 ER1 HR1 BR0 EL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 DL0 EL1 BR0 DL1 HR1 AR0,RWL 3 2)::
(makeTM BR1 CL1 AL1 BR1 DL0 EL1 BR0 DL1 HR1 DL0,RWL 3 2)::
(makeTM BR1 CL1 AL1 BR1 DL1 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 DL1 EL0 BR0 AR0 HR1 DL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 DL1 EL0 BR0 DL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 DR1 DL0 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 DR1 DL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 DR1 EL0 HR1 BR1 DR0 EL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 BR1 DR1 EL0 BR0 DL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 CL1 AL1 CR0 DR1 EL0 HR1 AR1 BR0 BL1,RWL 5 2)::
(makeTM BR1 CL1 AL1 CL1 DL0 AR0 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CL1 AL1 CL1 DL0 BR0 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 BR0 EL0 DL1 CL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 BR0 EL1 DL1 CL0 HR1 CL1,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 BL1 HR1 EL0 BR0 EL1 AL0,RWL 4 3)::
(makeTM BR1 CL1 AL1 DR0 BR1 AL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 BR1 AL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 BR1 BL1 HR1 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 CL1 AL1 DR0 BR1 CL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 BR1 CL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 BR1 DR0 HR1 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 CL1 AL1 DR0 BR1 ER0 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 CR0 AL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 AL1 DR0 DL1 HR1 BR1 ER0 EL1 CL0,RWL 14 2)::
(makeTM BR1 CL1 AL1 DR0 DR1 BR0 EL1 CR0 BL0 HR1,RWL 6 3)::
(makeTM BR1 CL1 AL1 DR1 BR1 CL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 CL1 AL1 DR1 BR1 CL1 HR1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 CL1 AL1 ER0 DR1 DL1 HR1 BR0 EL1 AL0,RWL 3 2)::
(makeTM BR1 CL1 AL1 EL1 AR1 DL0 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CL1 AL1 EL1 DL0 HR1 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CL1 AL1 EL1 DR0 CL1 BL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CL1 AL1 EL1 DR0 ER0 BL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 AL1 EL1 DL1 HR1 BL0 AR0 DL0 ER1,RWL 1 3)::
(makeTM BR1 CL1 AL1 ER1 DR0 CL0 DR1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CL1 BL0 AL1 DL0 HR1 DR1 ER0 BR0 AR0,RWL 2 3)::
(makeTM BR1 CL1 BL0 CR1 DL1 ER0 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 BL0 CR1 DR1 ER0 EL1 AR1 HR1 AL0,RWL 1 4)::
(makeTM BR1 CL1 BL0 CR1 DR1 ER0 EL1 BR1 HR1 AL0,RWL 4 2)::
(makeTM BR1 CL1 BL0 CR1 DR1 ER0 EL1 CR1 HR1 AL0,RWL 3 2)::
(makeTM BR1 CL1 BL1 AR0 DL1 EL1 AL1 ER0 HR1 DL0,RWL 4 2)::
(makeTM BR1 CL1 BL1 AR1 HR1 DL0 DR1 ER0 AL0 CR1,RWL 2 2)::
(makeTM BR1 CL1 BL1 AR1 HR1 DL0 DR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR1 CL1 BL1 AR1 HR1 DR1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 BL1 AR1 HR1 DR1 ER0 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 BL1 AR1 DR0 CL0 DR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL1 BL1 CL0 DL1 HR1 ER1 BR0 AL1 DR0,RWL 5 2)::
(makeTM BR1 CL1 BL1 CL1 CR1 DR0 HR1 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 CL1 BL1 CL1 DL0 AR0 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CL1 BL1 CR1 HR1 DR0 ER1 AL0 EL1 DL0,RWL 2 3)::
(makeTM BR1 CL1 CL0 HR1 HR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 HR1 AL0 DR1 CR1 ER0 EL1 AR0,RWL 1 4)::
(makeTM BR1 CL1 CL0 AL0 DR1 BR0 AL1 ER1 HR1 DR1,RWL 2 2)::
(makeTM BR1 CL1 CL0 AL0 DR1 BR0 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 AR0 DL0 BR0 AL1 EL0 DR1 HR1,RWL 5 2)::
(makeTM BR1 CL1 CL0 AR0 DL0 BR0 AL1 ER1 AR1 HR1,RWL 5 2)::
(makeTM BR1 CL1 CL0 AR0 DL0 DL1 ER1 AL1 HR1 DL1,RWL 3 2)::
(makeTM BR1 CL1 CL0 AR0 DL1 DL0 AL1 ER0 HR1 AR1,RWL 3 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DR0 ER1 HR1 AL1 BL1,RWL 5 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DL1 AL1 AL1 HR1 AL1,RWL 3 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DL1 AL1 BR1 HR1 AL1,RWL 6 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DL1 AL1 CR0 HR1 AL1,RWL 3 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DL1 AL1 ER0 HR1 AL1,RWL 6 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DL1 BL1 HR1 AL1 AL1,RWL 5 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DL1 BL1 HR1 AL1 CR0,RWL 5 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DL1 BL1 HR1 CR1 AL1,RWL 5 2)::
(makeTM BR1 CL1 CL0 AR0 EL0 DL1 CR1 AL1 HR1 AL1,RWL 3 2)::
(makeTM BR1 CL1 CL0 AR1 HR1 DR1 BL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 BL1 DR0 BL0 ER0 HR1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL1 CL0 BR1 DR1 CL1 HR1 ER1 AL1 BR0,RWL 2 2)::
(makeTM BR1 CL1 CL0 CL0 HR1 DR1 ER0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL0 CL0 DR1 BR0 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 DL0 HR1 AL1 ER1 DL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 CL1 CL0 DR0 AL0 AL1 ER0 HR1 BL0 AR0,RWL 2 4)::
(makeTM BR1 CL1 CL0 DL1 HR1 AL1 ER1 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 CL1 CL0 DL1 HR1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL1 CL0 DL1 DR1 BR0 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 DR1 HR1 AL1 BR1 EL1 BR0 DL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 DR1 HR1 DR1 BL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 ER0 HR1 DL0 AL1 DL1 EL1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL0 ER0 HR1 DR0 AL1 AL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 ER0 HR1 DR0 AL1 AL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL0 ER0 HR1 DL1 ER0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL0 ER0 HR1 DR1 EL0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL0 ER0 HR1 DR1 ER0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL0 ER0 AL1 DL0 AL1 HR1 BR1 CR0,RWL 35 2)::
(makeTM BR1 CL1 CL0 ER0 AL1 DL0 BR0 HR1 BR1 CR0,RWL 35 2)::
(makeTM BR1 CL1 CL0 EL1 HR1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL1 CL0 ER1 HR1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL1 CR0 HR1 DR0 EL1 DL1 AL0 AL0 AL1,RWL 4 2)::
(makeTM BR1 CL1 CR0 HR1 DL1 EL0 AL0 BR0 DR0 ER1,RWL 3 2)::
(makeTM BR1 CL1 CR0 HR1 DL1 ER0 EL0 BL0 AL0 EL1,RWL 10 2)::
(makeTM BR1 CL1 CR0 HR1 DR1 AL0 EL0 CR1 AL1 EL1,RWL 2 2)::
(makeTM BR1 CL1 CR0 AR0 DR0 AL1 DL1 EL0 BL1 HR1,RWL 4 2)::
(makeTM BR1 CL1 CR0 AR1 DL0 EL0 AL1 HR1 BR0 AL0,RWL 6 2)::
(makeTM BR1 CL1 CR0 AR1 DR1 ER1 AL0 DL1 HR1 BR0,RWL 3 2)::
(makeTM BR1 CL1 CR0 BR0 DL0 ER1 AL1 HR1 AR1 EL0,RWL 2 3)::
(makeTM BR1 CL1 CR0 BR1 DL0 ER0 AL1 HR1 BR1 DL0,RWL 5 3)::
(makeTM BR1 CL1 CR0 BR1 DL1 ER0 AR0 AL0 HR1 BR0,RWL 15 2)::
(makeTM BR1 CL1 CR0 CL0 DL1 EL0 AL0 HR1 ER1 AR1,RWL 1 4)::
(makeTM BR1 CL1 CR0 DL0 AL1 ER0 ER1 DL1 HR1 AR0,RWL 7 2)::
(makeTM BR1 CL1 CR0 DR0 AL1 BR1 EL1 AL0 DL0 HR1,RWL 2 2)::
(makeTM BR1 CL1 CR0 DL1 AL1 EL0 HR1 AL0 AR0 DL1,RWL 8 2)::
(makeTM BR1 CL1 CR0 EL0 DL1 DR0 AL1 BL0 HR1 BR1,RWL 1 4)::
(makeTM BR1 CL1 CR0 ER0 DL0 ER1 AL1 HR1 AR1 EL0,RWL 7 2)::
(makeTM BR1 CL1 CR0 ER0 DL1 DL0 AR1 BL1 HR1 AL0,RWL 3 2)::
(makeTM BR1 CL1 CR0 EL1 DL1 BR1 AL1 BL0 HR1 AL0,RWL 8 2)::
(makeTM BR1 CL1 CL1 HR1 HR1 DL0 DR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR1 CL1 CL1 HR1 HR1 DR1 ER0 CL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL1 HR1 DR0 CR1 DL1 EL0 AL1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 AL0 DR1 BL1 BR1 ER0 HR1 CR0,RWL 7 2)::
(makeTM BR1 CL1 CL1 AR1 DR0 CL0 DR1 EL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL1 BL0 DL0 AL1 DR1 ER0 AR0 HR1,RWL 2 3)::
(makeTM BR1 CL1 CL1 BR0 DL0 BL0 AR1 EL1 HR1 AL1,RWL 6 2)::
(makeTM BR1 CL1 CL1 BR0 ER0 DL0 CR1 AL0 HR1 AR1,RWL 6 2)::
(makeTM BR1 CL1 CL1 BR1 HR1 DL0 ER0 DL1 AL1 ER1,RWL 2 3)::
(makeTM BR1 CL1 CL1 BR1 HR1 DR0 EL0 DR1 AL1 EL1,RWL 2 2)::
(makeTM BR1 CL1 CL1 BR1 HR1 DL1 ER0 DL0 ER1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL1 BR1 HR1 DL1 ER0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL1 BR1 HR1 DR1 EL0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL1 BR1 HR1 DR1 ER0 DR0 EL1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL1 BR1 DR0 CL0 DR1 EL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CL1 CL1 BR1 DR1 CL0 ER0 HR1 ER1 AL1,RWL 2 3)::
(makeTM BR1 CL1 CL1 CL0 DR1 BR0 ER0 HR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL1 CR0 HR1 DL1 ER1 DL0 AR1 ER0,RWL 16 3)::
(makeTM BR1 CL1 CL1 CR0 DR1 AL1 BR1 EL1 HR1 DL0,RWL 4 3)::
(makeTM BR1 CL1 CL1 DL0 HR1 AL1 EL0 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 CL1 CL1 DL0 HR1 AL1 ER0 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 CL1 CL1 DL0 HR1 AL1 ER0 DL1 BR1 ER1,RWL 2 3)::
(makeTM BR1 CL1 CL1 DL0 HR1 AL1 ER1 DL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 CL1 CL1 DL0 HR1 BR1 ER0 DR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL1 DR0 HR1 AL1 AL0 ER1 CL0 BL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 HR1 AL1 AL0 ER1 CL0 DR1,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 HR1 AL1 EL0 DR1 BR1 EL1,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 HR1 BR1 ER1 AL0 EL1 DL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 AL1 BL0 ER0 DR1 HR1 AR0,RWL 6 2)::
(makeTM BR1 CL1 CL1 DR0 AL1 BL0 ER1 CR1 HR1 AR0,RWL 4 3)::
(makeTM BR1 CL1 CL1 DR0 AL1 DL1 EL1 AR0 BL0 HR1,RWL 3 2)::
(makeTM BR1 CL1 CL1 DR0 BR0 AL1 HR1 ER0 EL1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 BR1 AL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 BR1 AL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 BR1 CL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 CR0 AL1 EL1 DR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR0 ER1 AL1 HR1 CR0 BR1 EL0,RWL 7 3)::
(makeTM BR1 CL1 CL1 DL1 HR1 AL1 EL0 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 CL1 CL1 DL1 HR1 AL1 ER0 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 CL1 CL1 DL1 HR1 AL1 ER1 DL0 ER1 BR1,RWL 2 2)::
(makeTM BR1 CL1 CL1 DL1 HR1 BR0 DR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL1 DL1 EL0 AL1 HR1 AR0 ER1 DL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 DR1 HR1 AL1 EL0 DR0 EL1 BR1,RWL 2 2)::
(makeTM BR1 CL1 CL1 DR1 HR1 DL0 AR1 ER0 AL0 ER1,RWL 3 3)::
(makeTM BR1 CL1 CL1 DR1 HR1 DR1 ER0 BL0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL1 DR1 BR1 CL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 CL1 CL1 ER0 HR1 DL0 AR0 AR1 EL1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CL1 ER0 HR1 DL0 AR1 BR1 AL0 ER1,RWL 2 2)::
(makeTM BR1 CL1 CL1 ER0 HR1 DL0 AR1 ER0 AL0 ER1,RWL 2 3)::
(makeTM BR1 CL1 CL1 ER0 HR1 DR0 HR1 AL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL1 ER0 HR1 DR0 BR1 DL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL1 ER0 HR1 DL1 DR1 BR0 EL1 AL0,RWL 3 2)::
(makeTM BR1 CL1 CL1 ER0 AR1 DL0 AL1 AL0 CR0 HR1,RWL 11 2)::
(makeTM BR1 CL1 CL1 ER0 AR1 DL1 CL0 AL1 HR1 AR1,RWL 3 3)::
(makeTM BR1 CL1 CL1 ER0 DR1 CL0 AL1 AR0 HR1 BR0,RWL 9 2)::
(makeTM BR1 CL1 CL1 EL1 DL0 BL1 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 CL1 CL1 EL1 DL0 CL1 DR1 EL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CL1 CL1 EL1 DR0 CL1 BL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CL1 ER1 AL1 DL0 CL1 BR0 HR1 DR1,RWL 3 2)::
(makeTM BR1 CL1 CL1 ER1 DR0 CL0 DR1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CL1 CR1 HR1 AL0 DR1 AR1 ER0 EL1 AR0,RWL 1 4)::
(makeTM BR1 CL1 CR1 HR1 AL0 DR1 CR1 ER0 EL1 AR0,RWL 1 4)::
(makeTM BR1 CL1 CR1 HR1 AL0 DR1 EL1 ER0 DL1 AR0,RWL 1 4)::
(makeTM BR1 CL1 CR1 HR1 AL0 DR1 EL1 ER0 EL1 AR0,RWL 1 4)::
(makeTM BR1 CL1 CR1 HR1 AL0 DR1 ER1 ER0 EL1 AR0,RWL 1 4)::
(makeTM BR1 CL1 CR1 HR1 DR0 CR0 ER0 BL0 EL1 AL1,RWL 3 2)::
(makeTM BR1 CL1 CR1 HR1 DR0 CR1 DL1 EL0 AL1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CR1 HR1 DR0 DL0 ER1 AL0 DL1 BR0,RWL 8 2)::
(makeTM BR1 CL1 CR1 HR1 DL1 DL0 ER0 DL1 AL1 ER1,RWL 2 2)::
(makeTM BR1 CL1 CR1 HR1 DL1 DR0 ER1 AL0 AR1 EL0,RWL 1 3)::
(makeTM BR1 CL1 CR1 HR1 DL1 ER0 EL1 AL0 BL0 DR0,RWL 5 2)::
(makeTM BR1 CL1 CR1 HR1 DR1 BR0 EL1 CR0 AL0 DL0,RWL 4 2)::
(makeTM BR1 CL1 CR1 HR1 DR1 EL0 AL1 DR1 DR0 EL1,RWL 2 2)::
(makeTM BR1 CL1 CR1 AL0 DL1 BR0 HR1 EL1 CL1 BL1,RWL 6 2)::
(makeTM BR1 CL1 CR1 AR0 DL0 EL0 AL1 BL1 HR1 AR1,RWL 2 3)::
(makeTM BR1 CL1 CR1 AL1 DR1 CL0 ER0 HR1 AL1 AR1,RWL 6 2)::
(makeTM BR1 CL1 CR1 AL1 DR1 CL0 ER0 HR1 EL1 AR1,RWL 6 2)::
(makeTM BR1 CL1 CR1 AR1 AL0 DR0 HR1 ER1 AL1 AR0,RWL 6 3)::
(makeTM BR1 CL1 CR1 AR1 DL0 ER0 AL1 DL1 HR1 AR0,RWL 10 3)::
(makeTM BR1 CL1 CR1 AR1 DL1 DR1 BR0 EL1 HR1 AL0,RWL 2 4)::
(makeTM BR1 CL1 CR1 BL0 DR1 AL1 CL0 ER0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CL1 CR1 BR0 AL1 DL0 EL0 AL1 BL1 HR1,RWL 8 3)::
(makeTM BR1 CL1 CR1 BR0 DL0 AR0 HR1 EL1 AR1 EL0,RWL 4 2)::
(makeTM BR1 CL1 CR1 BR0 DL0 EL0 AR0 DL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CR1 BL1 DL1 DR0 ER0 AL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 CL1 CR1 BL1 DL1 DR0 ER1 AL0 HR1 BL1,RWL 2 3)::
(makeTM BR1 CL1 CR1 BL1 DL1 DR0 ER1 AL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 CL1 CR1 BR1 AL1 DR0 BR1 ER1 HR1 AL0,RWL 6 2)::
(makeTM BR1 CL1 CR1 BR1 DL0 CL1 AR1 EL1 HR1 AR0,RWL 2 2)::
(makeTM BR1 CL1 CR1 BR1 DR1 ER0 AL1 DL0 HR1 DL1,RWL 3 4)::
(makeTM BR1 CL1 CR1 CL0 DL0 ER0 BL1 AL0 BR1 HR1,RWL 3 3)::
(makeTM BR1 CL1 CR1 CL0 DL1 DR0 EL0 AL0 AR0 HR1,RWL 2 3)::
(makeTM BR1 CL1 CR1 CR0 AL0 DR0 HR1 ER1 AL1 EL1,RWL 2 2)::
(makeTM BR1 CL1 CR1 CR0 DL1 DR0 ER0 AL0 HR1 BR1,RWL 2 4)::
(makeTM BR1 CL1 CR1 DL0 AL1 BR0 AR0 EL1 AL0 HR1,RWL 8 2)::
(makeTM BR1 CL1 CR1 DL0 AL1 BR0 AR1 EL1 HR1 AL0,RWL 8 2)::
(makeTM BR1 CL1 CR1 DR0 AL0 BR1 EL1 AR0 DL1 HR1,RWL 1 4)::
(makeTM BR1 CL1 CR1 DR0 AL1 BR0 AL0 EL0 DL1 HR1,RWL 8 2)::
(makeTM BR1 CL1 CR1 DR0 DL0 AL1 HR1 ER0 EL1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CR1 DR0 DL0 ER0 BR1 AL1 HR1 BL0,RWL 3 2)::
(makeTM BR1 CL1 CR1 DR0 DL0 ER1 BR1 AL1 HR1 DL0,RWL 3 2)::
(makeTM BR1 CL1 CR1 DR1 AL1 BL0 CR0 ER0 HR1 AR0,RWL 2 2)::
(makeTM BR1 CL1 CR1 DR1 AL1 BL0 ER1 ER0 HR1 AR0,RWL 2 2)::
(makeTM BR1 CL1 CR1 EL0 DL0 AR0 HR1 EL1 AL0 BL1,RWL 18 2)::
(makeTM BR1 CL1 CR1 ER0 AL1 DL0 CR1 AL1 HR1 AR0,RWL 7 2)::
(makeTM BR1 CL1 CR1 ER0 AL1 DR1 HR1 AL0 BR1 AL1,RWL 3 3)::
(makeTM BR1 CL1 CR1 ER0 DL1 DR0 AL1 AL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 CL1 CR1 ER0 DR1 CL0 AL1 AR0 HR1 BR1,RWL 4 3)::
(makeTM BR1 CL1 CR1 ER0 DR1 CL0 AL1 AR0 HR1 DL0,RWL 15 2)::
(makeTM BR1 CL1 CR1 ER0 DR1 CL0 AL1 AR0 HR1 DL1,RWL 15 2)::
(makeTM BR1 CL1 CR1 EL1 DR0 CL1 BL1 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CL1 CR1 ER1 DL1 DR0 AL1 AL0 HR1 CL1,RWL 2 3)::
(makeTM BR1 CL1 CR1 ER1 DL1 DR0 AL1 AL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 CL1 CR1 ER1 DR1 CL0 AL1 AR0 HR1 DL0,RWL 4 3)::
(makeTM BR1 CR1 AL0 HR1 AL1 DR0 DL1 EL0 BR0 AL1,RWL 2 2)::
(makeTM BR1 CR1 AL0 HR1 AL1 DR0 DL1 EL0 BR0 CL1,RWL 2 2)::
(makeTM BR1 CR1 AL0 HR1 AL1 DR0 DL1 EL0 BR1 AL1,RWL 2 2)::
(makeTM BR1 CR1 AL0 HR1 AL1 DR0 DL1 EL0 BR1 CL1,RWL 2 2)::
(makeTM BR1 CR1 AL0 HR1 DR0 AL0 DL1 EL0 BR0 AL1,RWL 2 2)::
(makeTM BR1 CR1 AL0 HR1 DR0 DR0 DL1 EL0 BR0 AL1,RWL 2 2)::
(makeTM BR1 CR1 AL0 AR1 AL1 DR0 DL1 ER0 HR1 CL0,RWL 5 2)::
(makeTM BR1 CR1 AL0 BR0 DR0 CL0 EL1 ER0 AL1 HR1,RWL 12 2)::
(makeTM BR1 CR1 AL0 CR0 DL1 AL0 HR1 EL0 ER1 BR0,RWL 2 2)::
(makeTM BR1 CR1 AL0 CR0 DL1 EL0 HR1 AL1 AR1 BR0,RWL 2 2)::
(makeTM BR1 CR1 AL0 CL1 DR0 ER0 ER0 HR1 EL1 BL0,RWL 3 2)::
(makeTM BR1 CR1 AL0 DL0 BL1 BR0 EL0 HR1 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR1 AL0 DL1 DR0 BL1 EL1 CR0 CL0 HR1,RWL 4 2)::
(makeTM BR1 CR1 AL0 DR1 AL1 DL1 HR1 EL0 ER1 BR0,RWL 2 2)::
(makeTM BR1 CR1 AL0 DR1 BL1 EL0 HR1 CL1 ER1 BR0,RWL 2 2)::
(makeTM BR1 CR1 AL0 DR1 DL1 HR1 HR1 EL0 ER1 BR0,RWL 2 2)::
(makeTM BR1 CR1 AL0 EL0 DR0 BL0 DL1 AL1 HR1 BR0,RWL 2 2)::
(makeTM BR1 CR1 AL0 EL0 DR0 BL0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER0 CL1 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER0 DL0 CR1 AL1 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER1 CL1 DL0 DR1 BR0 HR1 AL0,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER1 CL1 DL0 DR1 BR0 HR1 AL1,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER1 CL1 DL0 DR1 BR0 HR1 CL1,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER1 CL1 DL0 DR1 BR0 HR1 DL0,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER1 DL0 CR1 AL1 DL1 HR1 BR0,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER1 DL1 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 AL0 ER1 DL1 EL0 AL0 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 CR1 AL1 HR1 AL0 DR0 DL1 EL0 CR0 AL1,RWL 2 2)::
(makeTM BR1 CR1 AL1 HR1 DR0 AL0 DL1 EL0 BR1 AL1,RWL 2 2)::
(makeTM BR1 CR1 AL1 AL0 AR1 DR0 DL1 ER0 HR1 BL0,RWL 5 2)::
(makeTM BR1 CR1 AL1 AL0 DR0 BR0 DL1 ER1 HR1 BL0,RWL 2 2)::
(makeTM BR1 CR1 AL1 AR0 BL0 DL1 CL1 EL1 DL0 HR1,RWL 10 2)::
(makeTM BR1 CR1 AL1 AL1 HR1 DR0 DL1 EL0 BR0 CL1,RWL 2 2)::
(makeTM BR1 CR1 AL1 AR1 HR1 DR0 DL1 ER0 HR1 BL0,RWL 5 2)::
(makeTM BR1 CR1 AL1 AR1 HR1 DR0 DL1 ER0 AL1 EL0,RWL 5 2)::
(makeTM BR1 CR1 AL1 AR1 HR1 DR0 EL1 ER0 DL1 BL0,RWL 5 2)::
(makeTM BR1 CR1 AL1 AR1 AL1 DR0 DL1 ER0 HR1 CL0,RWL 5 2)::
(makeTM BR1 CR1 AL1 AR1 DR0 AL0 DL1 ER0 HR1 BL0,RWL 5 2)::
(makeTM BR1 CR1 AL1 AR1 DL1 DR0 CL1 ER0 HR1 BL0,RWL 5 2)::
(makeTM BR1 CR1 AL1 CR1 BR1 DR0 DL1 ER0 HR1 BL0,RWL 4 2)::
(makeTM BR1 CR1 AL1 DL0 HR1 BL1 DR1 ER0 AL0 CR1,RWL 2 2)::
(makeTM BR1 CR1 AL1 DL0 BL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 CR1 AL1 DL0 DR0 BR0 AL0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 CR1 AL1 DL0 ER0 DR1 AL0 HR1 EL1 BR0,RWL 2 2)::
(makeTM BR1 CR1 AL1 DR0 BR1 CL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 CR1 AL1 DL1 BR0 AL0 CR0 EL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 CR1 AL1 DR1 AR1 BR0 EL1 CL0 HR1 DL0,RWL 1 3)::
(makeTM BR1 CR1 AL1 DR1 BR1 CL1 HR1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER0 BR0 DL1 HR1 CL1 EL1 CL0,RWL 2 3)::
(makeTM BR1 CR1 AL1 ER0 BR1 DL0 HR1 BR0 EL1 CL0,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER0 BR1 DL1 HR1 BR1 EL1 CL0,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER0 CL0 DL0 HR1 BR0 EL1 AL0,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER0 CL0 DL1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER1 HR1 DL0 DR1 BR0 EL1 CL0,RWL 3 2)::
(makeTM BR1 CR1 AL1 ER1 DL0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER1 DL0 CR0 DL1 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER1 DL0 CR1 BR1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER1 DR0 CR0 DL1 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER1 DR0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER1 DR0 CR0 DL1 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 CR1 AL1 ER1 DR0 CL1 AR0 BL0 DR1 HR1,RWL 1 3)::
(makeTM BR1 CR1 BL1 AL1 HR1 DL0 HR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR1 BL1 AR1 DL1 CR0 EL0 AL0 BL1 HR1,RWL 2 3)::
(makeTM BR1 CR1 BL1 AR1 DL1 ER0 HR1 AL0 DL0 ER1,RWL 2 2)::
(makeTM BR1 CR1 BL1 AR1 DL1 ER0 BL0 AL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 CR1 BL1 CL0 DL0 AL0 DR1 ER0 AR1 HR1,RWL 2 3)::
(makeTM BR1 CR1 BL1 CL0 DR1 EL0 ER0 HR1 CL0 AR1,RWL 4 2)::
(makeTM BR1 CR1 BL1 CR0 BR0 DL1 EL0 HR1 AL1 AL0,RWL 2 2)::
(makeTM BR1 CR1 CL0 AR0 DL1 BL1 AL1 EL1 DL0 HR1,RWL 4 3)::
(makeTM BR1 CR1 CL0 BR0 ER1 DL0 BL0 DL1 AR1 HR1,RWL 15 2)::
(makeTM BR1 CR1 CL0 BL1 ER1 DL0 BL1 AR0 AR0 HR1,RWL 3 2)::
(makeTM BR1 CR1 CL0 BR1 HR1 DR0 EL1 DR1 AL1 BL0,RWL 1 4)::
(makeTM BR1 CR1 CL0 BR1 DR1 CL1 HR1 ER1 AL1 BR0,RWL 2 2)::
(makeTM BR1 CR1 CL0 CL1 HR1 DL1 CR1 EL0 ER1 AR0,RWL 2 3)::
(makeTM BR1 CR1 CL0 DL1 ER1 DL0 BL1 AR0 AR1 HR1,RWL 4 2)::
(makeTM BR1 CR1 CL0 ER0 AL1 DL1 AR1 BL0 DR0 HR1,RWL 6 2)::
(makeTM BR1 CR1 CL0 ER0 DL0 CR1 AL1 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 CL0 ER0 DL1 CR1 ER1 BL1 HR1 AR0,RWL 6 3)::
(makeTM BR1 CR1 CR0 HR1 DL1 AR0 ER0 DL0 CL1 ER1,RWL 4 3)::
(makeTM BR1 CR1 CR0 HR1 DL1 EL1 EL0 DL0 AR1 ER0,RWL 4 2)::
(makeTM BR1 CR1 CR0 AL0 AL1 DR0 DL1 ER1 HR1 BL0,RWL 2 3)::
(makeTM BR1 CR1 CR0 BL0 DL1 AR1 BL1 ER1 HR1 DR0,RWL 2 4)::
(makeTM BR1 CR1 CR0 BL0 DL1 ER0 BL1 HR1 AR1 ER1,RWL 15 2)::
(makeTM BR1 CR1 CR0 BR1 DR0 ER0 DL1 AL1 HR1 DL0,RWL 4 3)::
(makeTM BR1 CR1 CR0 DL0 DL1 AR1 EL1 AL0 HR1 BL1,RWL 1 4)::
(makeTM BR1 CR1 CR0 DL1 DR1 AL0 EL1 AL0 HR1 BL0,RWL 1 3)::
(makeTM BR1 CR1 CR0 EL0 DR0 AL1 DL1 BL1 HR1 AL0,RWL 3 2)::
(makeTM BR1 CR1 CR0 EL0 DL1 DR0 AL0 BL0 HR1 BL1,RWL 2 2)::
(makeTM BR1 CR1 CR0 EL0 DL1 DR0 AL0 BL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 CR0 EL0 DL1 DR0 AL0 BL0 HR1 DR0,RWL 2 2)::
(makeTM BR1 CR1 CR0 EL1 DL1 DR0 AL0 BL0 HR1 AR0,RWL 3 2)::
(makeTM BR1 CR1 CR0 ER1 DL0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 CR0 ER1 DL0 CR0 DL1 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 CR1 CR0 ER1 DR0 CR0 DL1 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CR1 CR0 ER1 DR0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 CR0 ER1 DR0 CR0 DL1 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 CR1 CL1 HR1 AR1 DL0 EL0 CL0 ER1 AR0,RWL 2 3)::
(makeTM BR1 CR1 CL1 HR1 DL0 AR0 EL1 DL1 AL0 ER1,RWL 2 2)::
(makeTM BR1 CR1 CL1 HR1 DL1 AR0 ER0 DL0 CL1 ER1,RWL 4 3)::
(makeTM BR1 CR1 CL1 HR1 ER1 DR0 DL1 EL0 BR0 AL1,RWL 2 2)::
(makeTM BR1 CR1 CL1 HR1 ER1 DL1 EL1 CL0 AR0 EL0,RWL 15 2)::
(makeTM BR1 CR1 CL1 AL0 DR0 CR1 DL1 ER1 HR1 BL0,RWL 2 2)::
(makeTM BR1 CR1 CL1 AR0 DL0 BL1 AL1 EL0 BR0 HR1,RWL 2 4)::
(makeTM BR1 CR1 CL1 AR0 DL0 BL1 AL1 EL1 DL0 HR1,RWL 2 4)::
(makeTM BR1 CR1 CL1 AR0 DR0 DL1 AL1 ER0 HR1 DL0,RWL 29 2)::
(makeTM BR1 CR1 CL1 AR0 DL1 DR0 BR0 EL0 BL1 HR1,RWL 6 3)::
(makeTM BR1 CR1 CL1 AR0 DR1 BL0 AR0 ER1 CR1 HR1,RWL 2 3)::
(makeTM BR1 CR1 CL1 AR0 DR1 BL0 AL1 ER1 CR1 HR1,RWL 2 3)::
(makeTM BR1 CR1 CL1 AR0 DR1 BL0 AR1 ER0 DL1 HR1,RWL 2 3)::
(makeTM BR1 CR1 CL1 AR0 DR1 BL0 AR1 ER1 CR1 HR1,RWL 2 3)::
(makeTM BR1 CR1 CL1 AR0 DR1 BL0 BL0 ER1 CR1 HR1,RWL 2 3)::
(makeTM BR1 CR1 CL1 AR0 DR1 BL0 ER0 DL0 AR1 HR1,RWL 2 3)::
(makeTM BR1 CR1 CL1 AR0 DR1 DL1 AL1 ER0 HR1 DL0,RWL 9 2)::
(makeTM BR1 CR1 CL1 AR0 EL1 DL1 AL1 ER0 HR1 DL0,RWL 14 2)::
(makeTM BR1 CR1 CL1 AL1 DL1 AR0 ER1 BL0 HR1 DR1,RWL 4 3)::
(makeTM BR1 CR1 CL1 AR1 DL1 CR0 AL1 EL0 HR1 BL1,RWL 15 2)::
(makeTM BR1 CR1 CL1 BL0 AR1 DR1 HR1 ER0 EL1 BR0,RWL 5 2)::
(makeTM BR1 CR1 CL1 BR0 AR1 DL0 CL1 EL0 HR1 AL0,RWL 7 2)::
(makeTM BR1 CR1 CL1 BR0 DL1 AR0 AR1 EL1 BL0 HR1,RWL 2 4)::
(makeTM BR1 CR1 CL1 BR0 ER0 DL0 DR1 BL1 HR1 AR1,RWL 6 3)::
(makeTM BR1 CR1 CL1 BL1 DL1 AR0 AR1 EL0 CL1 HR1,RWL 5 2)::
(makeTM BR1 CR1 CL1 BL1 DR1 DL0 ER1 AR0 BL0 HR1,RWL 2 3)::
(makeTM BR1 CR1 CL1 BL1 ER1 DL0 BL1 AR0 HR1 AR0,RWL 2 3)::
(makeTM BR1 CR1 CL1 CL0 HR1 DL0 EL0 AL1 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR1 CL1 CR0 AR0 DL0 EL0 HR1 BL0 CL1,RWL 7 2)::
(makeTM BR1 CR1 CL1 CR0 AR0 DL0 EL0 HR1 BL0 CR1,RWL 7 2)::
(makeTM BR1 CR1 CL1 CR0 AR0 DL0 EL0 HR1 BL0 DL1,RWL 12 2)::
(makeTM BR1 CR1 CL1 CR0 AR0 DL0 EL0 HR1 BL0 EL1,RWL 7 3)::
(makeTM BR1 CR1 CL1 CL1 HR1 DL0 AR1 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 CR1 CL1 CL1 AR1 DL0 BL0 ER1 DR0 HR1,RWL 9 2)::
(makeTM BR1 CR1 CL1 DL0 AR1 BL0 DR1 ER0 BR1 HR1,RWL 3 3)::
(makeTM BR1 CR1 CL1 DL0 DR1 CL1 EL1 AR0 HR1 BL0,RWL 1 4)::
(makeTM BR1 CR1 CL1 DR0 AR1 BR1 DL1 ER0 HR1 BL0,RWL 5 2)::
(makeTM BR1 CR1 CL1 DR0 AR1 DL0 BL0 ER0 AL1 HR1,RWL 9 2)::
(makeTM BR1 CR1 CL1 DR0 AR1 DL0 BL0 ER1 DR0 HR1,RWL 9 2)::
(makeTM BR1 CR1 CL1 DR0 AR1 DL1 ER0 BR1 HR1 BL0,RWL 8 2)::
(makeTM BR1 CR1 CL1 DR0 ER1 DL0 BL1 AR0 HR1 AR1,RWL 3 2)::
(makeTM BR1 CR1 CL1 DR1 AR0 BL1 ER1 DL0 BR0 HR1,RWL 21 2)::
(makeTM BR1 CR1 CL1 DR1 AR1 BL0 ER0 AL0 HR1 BR1,RWL 7 2)::
(makeTM BR1 CR1 CL1 DR1 AR1 BL0 ER0 AR1 HR1 BR1,RWL 7 2)::
(makeTM BR1 CR1 CL1 DR1 DL0 AR0 ER0 BL0 AR1 HR1,RWL 3 3)::
(makeTM BR1 CR1 CL1 DR1 DL1 BL0 AR0 ER0 HR1 BL1,RWL 2 3)::
(makeTM BR1 CR1 CL1 DR1 EL0 DL1 AR1 BR0 HR1 BL0,RWL 4 2)::
(makeTM BR1 CR1 CL1 EL0 HR1 DL0 EL1 AR0 DR1 EL1,RWL 2 4)::
(makeTM BR1 CR1 CL1 EL0 DL1 DR0 HR1 EL1 AR1 BR0,RWL 2 2)::
(makeTM BR1 CR1 CL1 ER0 AR1 DL0 BL0 CL1 CR1 HR1,RWL 2 2)::
(makeTM BR1 CR1 CL1 ER0 CR0 DL0 AR1 AL0 AR1 HR1,RWL 10 2)::
(makeTM BR1 CR1 CL1 ER0 DL0 AR0 AL1 BL0 DR1 HR1,RWL 4 2)::
(makeTM BR1 CR1 CL1 ER0 DL1 AR1 AL1 DL1 HR1 BR1,RWL 4 2)::
(makeTM BR1 CR1 CL1 EL1 DL1 AR0 AR1 BL0 HR1 BL1,RWL 5 2)::
(makeTM BR1 CR1 CL1 EL1 DR1 BL0 HR1 AR1 AL0 ER0,RWL 6 2)::
(makeTM BR1 CR1 CL1 EL1 DR1 BL0 HR1 AR1 BL1 DR0,RWL 2 4)::
(makeTM BR1 CR1 CL1 ER1 HR1 DL0 AL1 AR0 DR1 BR1,RWL 4 2)::
(makeTM BR1 CR1 CL1 ER1 AR0 DL1 BR0 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 CL1 ER1 AR1 DL1 AR0 BL0 DR0 HR1,RWL 2 2)::
(makeTM BR1 CR1 CL1 ER1 DR0 BL0 BL1 AR1 CR0 HR1,RWL 3 3)::
(makeTM BR1 CR1 CL1 ER1 DL1 AR1 AL1 DL1 HR1 BR0,RWL 4 2)::
(makeTM BR1 CR1 CL1 ER1 DL1 BL0 AR0 CL1 AR0 HR1,RWL 2 3)::
(makeTM BR1 CR1 CL1 ER1 DL1 BL0 AR0 DR1 CR0 HR1,RWL 4 3)::
(makeTM BR1 CR1 CR1 HR1 DL1 AR0 ER1 DL1 AR1 EL0,RWL 2 3)::
(makeTM BR1 CR1 CR1 HR1 DL1 CR0 EL0 AL0 EL1 AR1,RWL 2 3)::
(makeTM BR1 CR1 CR1 HR1 DL1 ER0 HR1 AL0 DL0 ER1,RWL 2 2)::
(makeTM BR1 CR1 CR1 HR1 DL1 ER0 AR0 EL0 AL0 DR1,RWL 8 2)::
(makeTM BR1 CR1 CR1 AL0 AL1 DR0 DL1 ER1 HR1 BL0,RWL 2 3)::
(makeTM BR1 CR1 CR1 AL0 BL1 DR0 HR1 ER1 BL0 ER1,RWL 2 2)::
(makeTM BR1 CR1 CR1 AL0 BL1 DR0 EL0 DR1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CR1 CR1 AL0 DR0 BL0 DL1 ER0 HR1 BL1,RWL 2 2)::
(makeTM BR1 CR1 CR1 AL0 DR0 BL0 DL1 ER1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CR1 CR1 AR0 DR1 DL0 EL1 AL1 HR1 CL1,RWL 21 2)::
(makeTM BR1 CR1 CR1 BL0 DR1 AR0 EL1 ER0 HR1 BL1,RWL 34 3)::
(makeTM BR1 CR1 CR1 BL1 BL0 DR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 CR1 CR1 BL1 DL0 AR0 HR1 EL1 DL1 AL1,RWL 4 2)::
(makeTM BR1 CR1 CR1 BR1 DL0 CR0 DL1 EL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CR1 CR1 BR1 DL0 CL1 AR1 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CR1 CR1 BR1 DR0 CR0 DL1 EL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 CR1 CR1 CL0 DR0 AL0 DL1 ER0 HR1 AL1,RWL 2 2)::
(makeTM BR1 CR1 CR1 DL1 BL1 ER0 HR1 EL1 CL1 AL0,RWL 6 2)::
(makeTM BR1 CR1 CR1 DR1 DL1 EL0 AR0 EL1 HR1 AL1,RWL 5 2)::
(makeTM BR1 CR1 CR1 EL0 DR1 CR0 BL1 AL0 HR1 DL1,RWL 1 3)::
(makeTM BR1 CR1 CR1 ER0 DR0 HR1 DL1 EL0 BL1 AL0,RWL 2 3)::
(makeTM BR1 CR1 CR1 ER0 DR0 CR0 DL1 AL1 HR1 BL0,RWL 2 2)::
(makeTM BR1 CR1 CR1 ER0 DL1 AR1 AL1 DL1 HR1 BR1,RWL 4 2)::
(makeTM BR1 CR1 CR1 ER1 DL0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 CR1 ER1 DL0 CR0 DL1 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 CR1 CR1 ER1 DR0 CR0 DL1 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 CR1 CR1 ER1 DR0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 CR1 CR1 ER1 DR0 CR0 DL1 AL1 HR1 DR0,RWL 2 2)::
(makeTM BR1 CR1 CR1 ER1 DL1 AR1 AL1 DL1 HR1 BR0,RWL 4 2)::
(makeTM BR1 CR1 CR1 ER1 DL1 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DL0 BL0 CR1 DL1 ER0 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL0 BL0 CR1 DR1 HR1 AL1 EL0 ER1 CR0,RWL 14 2)::
(makeTM BR1 DL0 BL1 CR0 CL1 AL1 ER0 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 DL0 BL1 CR0 CL1 AL1 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR1 DL0 BL1 CR0 ER0 DR1 AL1 DL1 HR1 BR0,RWL 7 2)::
(makeTM BR1 DL0 BL1 CL1 AL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 BL1 CL1 AR1 HR1 CR0 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 DL0 BL1 CR1 HR1 AL1 DR1 ER0 AL0 CR1,RWL 2 2)::
(makeTM BR1 DL0 BL1 CR1 AL1 CR1 ER1 DL1 HR1 BR0,RWL 2 3)::
(makeTM BR1 DL0 BL1 CR1 AL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 BL1 CR1 BR1 DR0 EL1 BR0 AL0 HR1,RWL 13 2)::
(makeTM BR1 DL0 BL1 CR1 ER0 DL0 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL0 CL0 HR1 AL1 CR1 ER1 DL1 CL1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CL0 HR1 AL1 CR1 ER1 DL1 CR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CL0 HR1 DR0 CR1 EL1 CR0 AL0 BL1,RWL 10 2)::
(makeTM BR1 DL0 CL0 AR1 HR1 AL1 ER0 DL1 CL0 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL0 AR1 CR1 AL1 HR1 EL1 CR0 EL0,RWL 2 2)::
(makeTM BR1 DL0 CL0 AR1 ER0 DL1 CR1 AL1 HR1 AR0,RWL 4 2)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 HR1 EL1 AL1 CL1,RWL 3 2)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 HR1 EL1 AL1 CR1,RWL 3 2)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 HR1 EL1 BR1 AL0,RWL 3 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 HR1 EL1 CL0 AL0,RWL 6 2)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL0 AL1 AR0 HR1,RWL 4 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL0 AL1 AL1 HR1,RWL 4 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL0 AL1 CR0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL0 DR0 AL1 HR1,RWL 4 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 ER0 AL1 BR0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 ER0 AL1 DR0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL1 AL1 AL1 HR1,RWL 2 4)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL1 AL1 AR1 HR1,RWL 4 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL1 AL1 BR0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL1 AL1 CL0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL1 AL1 CR0 HR1,RWL 4 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 ER1 AL1 BR0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 ER1 AL1 DR0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 BR0 CL1 DR1 EL1 BR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 DL0 CL0 BR0 DR1 CL1 BR1 EL0 HR1 AL1,RWL 3 3)::
(makeTM BR1 DL0 CL0 BR1 HR1 AL1 DR1 ER1 AL1 BR0,RWL 3 2)::
(makeTM BR1 DL0 CL0 CR0 AR1 AL1 EL1 AL1 HR1 CL1,RWL 6 2)::
(makeTM BR1 DL0 CL0 CR0 AR1 AL1 EL1 BR1 HR1 CL1,RWL 6 2)::
(makeTM BR1 DL0 CL0 CR0 CL1 AL1 ER0 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 DL0 CL0 CR0 EL1 DR1 CR0 BL0 AL1 HR1,RWL 15 2)::
(makeTM BR1 DL0 CL0 DR0 AR0 DL1 EL1 CR0 AL1 HR1,RWL 4 2)::
(makeTM BR1 DL0 CL0 DR0 AL1 BL0 CL1 ER0 AR0 HR1,RWL 2 2)::
(makeTM BR1 DL0 CL0 DR0 AL1 BL1 CL1 ER0 AR0 HR1,RWL 4 3)::
(makeTM BR1 DL0 CL0 DR0 AL1 CR1 EL1 CR0 BL1 HR1,RWL 13 2)::
(makeTM BR1 DL0 CL0 DR0 EL1 AL1 CR0 BL1 AL1 HR1,RWL 8 2)::
(makeTM BR1 DL0 CL0 DR1 ER1 AL1 AR1 CL1 HR1 CR0,RWL 3 2)::
(makeTM BR1 DL0 CL0 ER0 HR1 DL1 EL0 AL1 AR1 BL1,RWL 18 2)::
(makeTM BR1 DL0 CL0 ER0 HR1 DL1 EL1 AR0 DR1 CR1,RWL 4 2)::
(makeTM BR1 DL0 CL0 ER0 AL1 CR1 DR1 CL1 HR1 CR0,RWL 3 4)::
(makeTM BR1 DL0 CL0 ER0 AL1 DL1 CR1 CL1 HR1 AR0,RWL 7 2)::
(makeTM BR1 DL0 CL0 ER0 DL1 CR1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL0 CL0 ER0 DR1 CR0 AL1 CL0 CR1 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 ER0 EL1 DR1 CR1 BR1 HR1 AL0,RWL 4 2)::
(makeTM BR1 DL0 CL0 ER1 AL1 CR1 CR0 DL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 DL0 CL0 ER1 DR1 CR1 AL1 BL0 CR0 HR1,RWL 2 2)::
(makeTM BR1 DL0 CR0 HR1 CL1 AR0 DR1 EL1 DL1 AL0,RWL 13 2)::
(makeTM BR1 DL0 CR0 HR1 CL1 AR1 EL0 DL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 DL0 CR0 HR1 CL1 DL0 ER0 DL1 AL0 AR0,RWL 2 3)::
(makeTM BR1 DL0 CR0 HR1 CL1 DR1 BR1 EL1 DR1 AL0,RWL 3 2)::
(makeTM BR1 DL0 CR0 HR1 DL1 AR0 DR1 EL1 DL1 AL0,RWL 13 2)::
(makeTM BR1 DL0 CR0 HR1 DR1 AL0 EL1 BR0 AL0 DL0,RWL 5 3)::
(makeTM BR1 DL0 CR0 HR1 DR1 CR1 EL1 AR0 CL0 AL0,RWL 1 4)::
(makeTM BR1 DL0 CR0 HR1 DR1 CR1 EL1 AR0 CR1 AL0,RWL 2 3)::
(makeTM BR1 DL0 CR0 HR1 DR1 CR1 EL1 AR0 ER0 AL0,RWL 2 3)::
(makeTM BR1 DL0 CR0 HR1 DR1 ER1 EL1 AR1 CL1 AL0,RWL 4 2)::
(makeTM BR1 DL0 CR0 AL0 AL1 ER1 BL1 CL0 AR0 HR1,RWL 16 2)::
(makeTM BR1 DL0 CR0 AL0 DR0 HR1 DL1 EL0 AR1 AL0,RWL 3 3)::
(makeTM BR1 DL0 CR0 AR0 CL1 DL1 EL1 HR1 BR1 AR0,RWL 2 4)::
(makeTM BR1 DL0 CR0 AR0 CL1 DL1 EL1 HR1 ER1 AR0,RWL 2 4)::
(makeTM BR1 DL0 CR0 AR0 DL1 AR0 EL0 HR1 AL1 CR0,RWL 5 3)::
(makeTM BR1 DL0 CR0 AL1 BL1 CR1 EL1 BR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 DL0 CR0 AR1 DL1 CR1 EL1 BL0 HR1 AL0,RWL 16 2)::
(makeTM BR1 DL0 CR0 AR1 DR1 BR1 AL1 EL0 HR1 AR0,RWL 6 2)::
(makeTM BR1 DL0 CR0 AR1 DR1 BR1 AL1 EL1 HR1 CL0,RWL 6 2)::
(makeTM BR1 DL0 CR0 AR1 DR1 BR1 AL1 EL1 HR1 CR0,RWL 6 2)::
(makeTM BR1 DL0 CR0 AR1 DR1 CL1 AL1 EL0 HR1 AR0,RWL 6 2)::
(makeTM BR1 DL0 CR0 BR0 CL1 AL0 HR1 ER1 ER0 BR0,RWL 2 2)::
(makeTM BR1 DL0 CR0 BL1 DR0 CR1 EL1 BL0 AL1 HR1,RWL 2 3)::
(makeTM BR1 DL0 CR0 BR1 CL1 AL0 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 DL0 CR0 BR1 CL1 AL0 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DL0 CR0 BR1 CL1 AL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 DL0 CR0 BR1 DL0 AR0 EL1 HR1 BR1 CL1,RWL 5 3)::
(makeTM BR1 DL0 CR0 BR1 DL1 CR1 AL1 EL0 HR1 CR0,RWL 6 2)::
(makeTM BR1 DL0 CR0 BR1 DL1 CR1 AL1 EL1 HR1 AL1,RWL 6 2)::
(makeTM BR1 DL0 CR0 BR1 DL1 DR0 AL1 ER1 AR0 HR1,RWL 3 3)::
(makeTM BR1 DL0 CR0 CR0 CL1 AL1 ER0 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 DL0 CR0 CL1 DR1 AL0 AL1 ER0 CR0 HR1,RWL 5 3)::
(makeTM BR1 DL0 CR0 CR1 AL1 AR1 ER1 AL0 DR0 HR1,RWL 14 2)::
(makeTM BR1 DL0 CR0 CR1 AL1 ER0 HR1 EL0 BR1 EL1,RWL 2 3)::
(makeTM BR1 DL0 CR0 CR1 DR1 HR1 AL1 EL0 BR0 CR0,RWL 4 2)::
(makeTM BR1 DL0 CR0 CR1 DR1 HR1 AL1 EL0 ER1 CR0,RWL 5 2)::
(makeTM BR1 DL0 CR0 DR0 AL1 CL1 EL1 AR0 CL0 HR1,RWL 1 4)::
(makeTM BR1 DL0 CR0 DR0 DR1 ER0 AL1 CL1 HR1 DR1,RWL 5 2)::
(makeTM BR1 DL0 CR0 DL1 AL1 AR0 EL1 BL1 AL0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CR0 DL1 AL1 CR1 HR1 EL0 BR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CR0 DL1 AL1 CR1 ER0 DL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 DL0 CR0 DL1 AL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CR0 DL1 DR1 AL0 EL1 BR0 HR1 CL1,RWL 3 3)::
(makeTM BR1 DL0 CR0 DR1 CL1 AL1 BR1 EL0 HR1 BR1,RWL 6 2)::
(makeTM BR1 DL0 CR0 DR1 CL1 AL1 BR1 EL1 HR1 AR0,RWL 6 2)::
(makeTM BR1 DL0 CR0 DR1 DL1 HR1 AL1 ER0 CL0 DR0,RWL 5 2)::
(makeTM BR1 DL0 CR0 DR1 DR1 HR1 AL1 ER0 DL1 BR0,RWL 3 2)::
(makeTM BR1 DL0 CR0 EL1 CL1 AL0 HR1 ER1 ER0 BR0,RWL 2 2)::
(makeTM BR1 DL0 CR0 EL1 CL1 DR0 HR1 BR0 AL1 AL0,RWL 3 2)::
(makeTM BR1 DL0 CR0 EL1 DL1 CR1 EL1 BR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 DL0 CR0 EL1 DR1 AL0 AL1 BR0 HR1 AL0,RWL 5 3)::
(makeTM BR1 DL0 CR0 ER1 DR1 AR1 AL1 CR0 AR1 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL1 HR1 ER0 AR1 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL0 CL1 HR1 ER1 AR1 ER1 CL1 AL1 CR0,RWL 9 2)::
(makeTM BR1 DL0 CL1 AL0 HR1 AL1 DR1 ER0 BR1 CR0,RWL 3 2)::
(makeTM BR1 DL0 CL1 AL0 BL1 AR1 HR1 ER1 DL1 BR0,RWL 2 2)::
(makeTM BR1 DL0 CL1 AL0 DR1 AR1 HR1 ER0 BL1 ER1,RWL 2 3)::
(makeTM BR1 DL0 CL1 AL0 DR1 CL1 HR1 ER0 BL1 ER1,RWL 2 3)::
(makeTM BR1 DL0 CL1 AR0 HR1 AL1 AR1 EL1 AR0 BL0,RWL 17 2)::
(makeTM BR1 DL0 CL1 AR0 AR1 BL0 ER1 DR1 CR1 HR1,RWL 6 2)::
(makeTM BR1 DL0 CL1 AR0 AR1 BL1 CR0 EL1 CL0 HR1,RWL 8 2)::
(makeTM BR1 DL0 CL1 AR0 DL1 CR0 EL1 HR1 AL1 EL0,RWL 4 2)::
(makeTM BR1 DL0 CL1 AL1 HR1 BR0 DR1 ER0 AL0 BR0,RWL 2 2)::
(makeTM BR1 DL0 CL1 AL1 HR1 BR1 DR1 ER0 AL0 BR0,RWL 2 2)::
(makeTM BR1 DL0 CL1 AL1 AR0 BL1 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 AL1 BR0 BL1 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 AL1 BR1 BL1 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 AL1 BR1 BL1 DR1 EL0 HR1 CR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 AL1 DL0 BL1 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 AL1 DL1 BL1 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 AL1 DR1 BL1 CR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 AL1 DR1 BL1 DR1 EL0 HR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 AR1 HR1 DL1 ER1 CL0 BL0 AR0,RWL 2 3)::
(makeTM BR1 DL0 CL1 AR1 HR1 DL1 ER1 CL0 BR1 AR0,RWL 2 3)::
(makeTM BR1 DL0 CL1 AR1 AL1 CL1 CL1 EL1 HR1 BR0,RWL 6 2)::
(makeTM BR1 DL0 CL1 AR1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL0 CL1 AR1 ER0 AL1 HR1 CR0 EL1 AL0,RWL 3 2)::
(makeTM BR1 DL0 CL1 BR0 EL1 DL1 EL1 HR1 ER1 AR0,RWL 3 3)::
(makeTM BR1 DL0 CL1 BR0 ER1 DL1 EL1 HR1 BR1 AR0,RWL 24 2)::
(makeTM BR1 DL0 CL1 BL1 HR1 DL1 ER1 EL0 AR1 AR0,RWL 3 2)::
(makeTM BR1 DL0 CL1 BL1 ER1 AR1 HR1 AL1 BR1 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BL1 ER1 AR1 HR1 AL1 CL0 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 HR1 AL1 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 HR1 AL1 BR0 DL1 HR1 HR1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 HR1 AL1 EL0 DR1 BR0 EL1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 HR1 AL1 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 HR1 AL1 ER0 DL1 BL0 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 HR1 AL1 ER0 DL1 CL1 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 HR1 AL1 EL1 DL1 ER0 BR0,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 AL0 AL1 ER0 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 AR0 AL1 ER0 DL1 HR1 CL0,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 BR0 AL1 ER0 DL1 HR1 CL0,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 BR0 AL1 ER0 DL1 HR1 CL1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 DL1 AL1 HR1 EL0 AR0 CR1,RWL 2 3)::
(makeTM BR1 DL0 CL1 BR1 DL1 AL1 ER1 DL1 HR1 BR0,RWL 3 3)::
(makeTM BR1 DL0 CL1 BR1 DR1 AL1 ER1 DL1 HR1 BR0,RWL 3 3)::
(makeTM BR1 DL0 CL1 BR1 DR1 CR1 AL1 EL0 HR1 CR0,RWL 6 2)::
(makeTM BR1 DL0 CL1 BR1 EL0 AL1 HR1 CR1 BR0 EL1,RWL 2 2)::
(makeTM BR1 DL0 CL1 BR1 EL0 AL1 HR1 EL0 AR0 BR0,RWL 2 3)::
(makeTM BR1 DL0 CL1 BR1 ER0 AL1 CL0 DL1 BR0 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL1 CR0 AL0 AL1 HR1 EL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 DL0 CL1 CR0 AL0 AL1 ER0 DL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DL0 CL1 CR0 AL0 AL1 ER0 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 DL0 CL1 CR0 AR0 DL1 EL0 HR1 CR1 BR0,RWL 6 3)::
(makeTM BR1 DL0 CL1 CR0 AR0 DL1 EL0 HR1 CR1 EL0,RWL 6 3)::
(makeTM BR1 DL0 CL1 CR0 AR0 DL1 EL1 HR1 ER1 AR0,RWL 6 3)::
(makeTM BR1 DL0 CL1 CR0 AR1 AR0 EL0 HR1 CR1 EL1,RWL 1 4)::
(makeTM BR1 DL0 CL1 CR0 DR0 BR1 BL0 EL1 AL0 HR1,RWL 3 2)::
(makeTM BR1 DL0 CL1 CR0 ER0 DR1 AL1 BL1 HR1 DL1,RWL 14 2)::
(makeTM BR1 DL0 CL1 CL1 AL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CL1 CR1 HR1 AL1 AR0 EL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 DL0 CL1 CR1 HR1 AL1 DR1 EL0 DR1 AR0,RWL 2 3)::
(makeTM BR1 DL0 CL1 CR1 HR1 AL1 ER1 EL0 DR1 AR0,RWL 2 3)::
(makeTM BR1 DL0 CL1 CR1 AL1 CR0 HR1 EL0 BR0 BL1,RWL 6 3)::
(makeTM BR1 DL0 CL1 CR1 AL1 CR0 HR1 EL0 ER1 BL1,RWL 15 2)::
(makeTM BR1 DL0 CL1 CR1 AL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CL1 CR1 AL1 DR1 ER0 BR0 CL0 HR1,RWL 6 3)::
(makeTM BR1 DL0 CL1 DL0 ER0 BR1 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL0 CL1 DR0 HR1 AL1 BR1 EL1 CL0 CL0,RWL 8 2)::
(makeTM BR1 DL0 CL1 DR0 HR1 AL1 BR1 EL1 CL0 DR0,RWL 8 2)::
(makeTM BR1 DL0 CL1 DR0 HR1 AL1 BR1 EL1 DR1 CL0,RWL 8 2)::
(makeTM BR1 DL0 CL1 DR0 HR1 DL1 BR0 EL0 AR1 ER0,RWL 2 3)::
(makeTM BR1 DL0 CL1 DR0 HR1 DL1 CR1 EL0 AR1 ER0,RWL 2 3)::
(makeTM BR1 DL0 CL1 DR0 AR0 BL0 EL1 CR0 AL1 HR1,RWL 4 3)::
(makeTM BR1 DL0 CL1 DR0 AL1 BL1 AR0 EL1 DL0 HR1,RWL 9 2)::
(makeTM BR1 DL0 CL1 DR0 AL1 CL0 AR1 ER0 CR1 HR1,RWL 6 2)::
(makeTM BR1 DL0 CL1 DR0 AL1 CL1 ER1 CL0 AR0 HR1,RWL 2 4)::
(makeTM BR1 DL0 CL1 DR0 AL1 CR1 EL1 CR0 BL1 HR1,RWL 3 4)::
(makeTM BR1 DL0 CL1 DR0 DR1 CL0 BL0 ER0 AR1 HR1,RWL 4 2)::
(makeTM BR1 DL0 CL1 DL1 HR1 AL1 ER0 DL1 CL1 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL1 DR1 HR1 AL1 ER0 DL1 CL1 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL1 DR1 AL1 DR0 HR1 ER0 CL1 BL0,RWL 2 3)::
(makeTM BR1 DL0 CL1 DR1 AL1 DR0 HR1 ER0 CL1 EL0,RWL 2 3)::
(makeTM BR1 DL0 CL1 DR1 BR1 CL1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL1 DR1 DR0 BL0 AR0 ER1 CR1 HR1,RWL 5 2)::
(makeTM BR1 DL0 CL1 DR1 ER1 AL1 AR1 CL1 HR1 CR0,RWL 3 2)::
(makeTM BR1 DL0 CL1 EL0 AR0 BL1 CR1 BR0 HR1 AL0,RWL 4 3)::
(makeTM BR1 DL0 CL1 EL0 AR0 BL1 CR1 CR1 HR1 AL0,RWL 4 3)::
(makeTM BR1 DL0 CL1 EL0 AR1 BL0 HR1 CR1 ER1 AR0,RWL 14 2)::
(makeTM BR1 DL0 CL1 EL0 DR0 BL0 HR1 ER1 AR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 EL0 DR0 BL0 AR1 DR1 HR1 AR0,RWL 5 2)::
(makeTM BR1 DL0 CL1 EL0 DR0 BL1 AR0 DR1 HR1 CL1,RWL 6 4)::
(makeTM BR1 DL0 CL1 ER0 HR1 DR1 AL1 DL1 EL1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CL1 ER0 AL1 AR0 BR0 CL1 HR1 DR1,RWL 5 2)::
(makeTM BR1 DL0 CL1 ER0 AL1 AR0 CL1 HR1 BL1 CR0,RWL 4 3)::
(makeTM BR1 DL0 CL1 ER0 AL1 AR0 CL1 HR1 DL1 CR0,RWL 4 3)::
(makeTM BR1 DL0 CL1 ER0 AL1 AR1 HR1 CR0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL0 CL1 ER0 BR1 AR1 HR1 BR0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL0 CL1 ER0 DR1 CR0 AL1 CL0 CR1 HR1,RWL 2 3)::
(makeTM BR1 DL0 CL1 ER0 DR1 CL1 HR1 AR1 CL0 ER1,RWL 3 2)::
(makeTM BR1 DL0 CL1 ER0 DR1 CL1 HR1 BR1 AL0 ER1,RWL 2 2)::
(makeTM BR1 DL0 CL1 EL1 AR1 BL0 HR1 CR1 AL0 ER0,RWL 5 3)::
(makeTM BR1 DL0 CL1 EL1 CR1 AR1 HR1 AL1 CL0 EL0,RWL 2 2)::
(makeTM BR1 DL0 CL1 EL1 CR1 AR1 HR1 AL1 CR0 EL0,RWL 2 2)::
(makeTM BR1 DL0 CL1 EL1 DR1 BL0 HR1 AR1 AL0 ER0,RWL 19 2)::
(makeTM BR1 DL0 CL1 ER1 DL0 CL1 AR1 DR0 HR1 AR0,RWL 3 3)::
(makeTM BR1 DL0 CL1 ER1 DR1 AR1 AL1 CR0 AR1 HR1,RWL 2 3)::
(makeTM BR1 DL0 CR1 HR1 AL0 AR1 CL1 ER1 DR0 ER1,RWL 5 2)::
(makeTM BR1 DL0 CR1 HR1 AL0 ER0 DL1 CL1 BR0 DR1,RWL 5 2)::
(makeTM BR1 DL0 CR1 HR1 AL0 ER1 AR0 CL1 CL1 ER0,RWL 9 2)::
(makeTM BR1 DL0 CR1 HR1 AL0 ER1 CL1 DR1 BR1 DR0,RWL 5 2)::
(makeTM BR1 DL0 CR1 HR1 AL1 DR0 EL0 CR1 AR1 EL0,RWL 4 2)::
(makeTM BR1 DL0 CR1 HR1 DR0 AL0 ER1 DL1 CL1 AR0,RWL 13 2)::
(makeTM BR1 DL0 CR1 HR1 DL1 ER0 EL0 DL1 BR0 AL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 AL0 AL1 ER0 HR1 BR1 EL1 BL0,RWL 2 3)::
(makeTM BR1 DL0 CR1 AL0 DL1 AR0 BL1 EL1 HR1 CL1,RWL 3 2)::
(makeTM BR1 DL0 CR1 AR0 AL0 EL0 DR1 CL1 HR1 AL1,RWL 2 3)::
(makeTM BR1 DL0 CR1 AR0 AL1 BR1 EL1 BL1 HR1 CL0,RWL 4 2)::
(makeTM BR1 DL0 CR1 AR0 AL1 CL0 CL1 EL0 BR0 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 AR0 AL1 EL1 CR0 CL0 HR1 AL1,RWL 4 2)::
(makeTM BR1 DL0 CR1 AR0 DL1 BR1 BR1 EL1 HR1 AL1,RWL 3 2)::
(makeTM BR1 DL0 CR1 AL1 BL1 EL1 DR1 EL0 HR1 BR0,RWL 2 3)::
(makeTM BR1 DL0 CR1 AL1 DL1 ER0 HR1 EL0 AR1 CR1,RWL 5 3)::
(makeTM BR1 DL0 CR1 AL1 DR1 ER0 AL0 BL1 AR1 HR1,RWL 3 2)::
(makeTM BR1 DL0 CR1 AR1 AL1 AL1 CL0 ER1 DR0 HR1,RWL 9 2)::
(makeTM BR1 DL0 CR1 AR1 AL1 BR0 EL0 BL1 HR1 BR1,RWL 14 2)::
(makeTM BR1 DL0 CR1 AR1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL0 CR1 AR1 AL1 DR0 CL0 ER1 DR0 HR1,RWL 9 2)::
(makeTM BR1 DL0 CR1 BL0 AL1 AR0 BR0 EL1 BL0 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BL0 AL1 ER0 BR0 AL1 AR0 HR1,RWL 3 3)::
(makeTM BR1 DL0 CR1 BL0 AL1 ER1 BR1 CR0 AR0 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BL0 DR1 HR1 AL0 ER1 AL1 BR0,RWL 3 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 AR0 AL1 EL0 BL1 HR1,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 AR0 AL1 EL1 AL1 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 BL1 CL0 ER1 DR1 HR1,RWL 1 3)::
(makeTM BR1 DL0 CR1 BR0 AL1 CL1 BL1 EL0 BL0 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 CL1 BL1 EL0 BL1 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 CL1 BL1 EL0 CL1 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 CL1 BL1 EL1 AR0 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 DR0 CL1 EL0 BL1 HR1,RWL 6 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 EL1 BL1 DL0 HR1 CL1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BR0 AL1 EL1 CL1 DR0 HR1 AR0,RWL 2 3)::
(makeTM BR1 DL0 CR1 BR0 DR1 DR0 AL1 ER1 AR0 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BR0 DR1 EL0 AL1 DL1 HR1 CL1,RWL 20 2)::
(makeTM BR1 DL0 CR1 BR0 DR1 ER1 AL1 DL0 DR0 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 BL1 AL0 ER0 HR1 BL1 AL1 ER1,RWL 2 3)::
(makeTM BR1 DL0 CR1 BL1 AL1 DR0 ER1 BL0 AR1 HR1,RWL 3 4)::
(makeTM BR1 DL0 CR1 BL1 BL0 DR1 HR1 ER0 AL0 ER1,RWL 2 2)::
(makeTM BR1 DL0 CR1 BL1 DL1 ER0 HR1 BL1 AL1 ER1,RWL 2 3)::
(makeTM BR1 DL0 CR1 BL1 DR1 CR1 AL1 EL0 HR1 CR0,RWL 3 2)::
(makeTM BR1 DL0 CR1 BR1 AL0 ER1 BL1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CR0 EL1 BL0 AL0 HR1,RWL 3 3)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 EL0 AR0 BL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 EL0 AR0 CR1,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 EL0 CL1 DL1,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 ER0 ER1 CL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 EL1 AL0 DL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 EL1 AL1 DL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 EL1 BR0 DL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 EL1 BL1 DL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 HR1 EL1 CR0 DL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 CL1 ER1 DR0 HR1 CL0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 DR0 EL1 BR0 CL0 HR1,RWL 2 4)::
(makeTM BR1 DL0 CR1 BR1 AL1 DR0 ER1 CL0 BR0 HR1,RWL 2 4)::
(makeTM BR1 DL0 CR1 BR1 AL1 DR1 EL0 BR0 HR1 CL1,RWL 14 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 EL0 CL1 BL1 HR1 BR0,RWL 7 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 ER0 HR1 CL0 CL1 ER0,RWL 6 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 ER1 CL1 CR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 DL0 CR1 BR1 DL1 AR0 BL1 EL0 HR1 CL1,RWL 2 4)::
(makeTM BR1 DL0 CR1 BR1 DL1 CL1 AL1 EL0 HR1 CR0,RWL 3 2)::
(makeTM BR1 DL0 CR1 BR1 DL1 CL1 AL1 EL1 HR1 AL1,RWL 3 2)::
(makeTM BR1 DL0 CR1 BR1 DL1 CL1 DR1 EL1 HR1 AL1,RWL 3 2)::
(makeTM BR1 DL0 CR1 BR1 DR1 BL0 AL1 EL0 HR1 CR0,RWL 6 2)::
(makeTM BR1 DL0 CR1 BR1 DR1 CR1 AL1 EL0 HR1 CR0,RWL 6 2)::
(makeTM BR1 DL0 CR1 CL0 AL0 ER0 AL1 BL1 AR1 HR1,RWL 6 3)::
(makeTM BR1 DL0 CR1 CL0 AL1 ER0 HR1 EL1 AL0 BR1,RWL 5 2)::
(makeTM BR1 DL0 CR1 CL0 AL1 ER0 AL0 BL1 AR1 HR1,RWL 24 2)::
(makeTM BR1 DL0 CR1 CL0 AL1 ER0 AR1 BL0 BR1 HR1,RWL 4 3)::
(makeTM BR1 DL0 CR1 CL0 AL1 ER0 ER1 BL0 BR1 HR1,RWL 4 3)::
(makeTM BR1 DL0 CR1 CR0 AL1 AR1 HR1 EL0 ER1 CL0,RWL 2 3)::
(makeTM BR1 DL0 CR1 CR0 AL1 ER0 HR1 CL0 AL0 AR1,RWL 1 4)::
(makeTM BR1 DL0 CR1 CR0 DR1 BR1 EL1 CL0 HR1 AL0,RWL 32 2)::
(makeTM BR1 DL0 CR1 CR0 DR1 EL1 AL1 BR0 HR1 AL0,RWL 3 2)::
(makeTM BR1 DL0 CR1 CL1 AL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CR1 CL1 AL1 ER0 HR1 BL1 AL0 AR1,RWL 3 3)::
(makeTM BR1 DL0 CR1 CL1 AL1 ER0 HR1 BL1 EL0 AR1,RWL 3 3)::
(makeTM BR1 DL0 CR1 CL1 DL0 AR0 BL1 EL0 HR1 DR1,RWL 5 2)::
(makeTM BR1 DL0 CR1 CL1 DL0 AR0 BL1 EL1 HR1 CL1,RWL 5 2)::
(makeTM BR1 DL0 CR1 CR1 AL1 CR1 ER1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CR1 CR1 DR1 HR1 AL1 EL0 ER1 CR0,RWL 14 2)::
(makeTM BR1 DL0 CR1 DR0 DL1 HR1 ER1 AL1 EL1 BL0,RWL 4 3)::
(makeTM BR1 DL0 CR1 DR0 DL1 AL1 HR1 EL0 ER1 BR1,RWL 3 2)::
(makeTM BR1 DL0 CR1 DR1 AL1 BR1 ER1 CL0 AR0 HR1,RWL 3 3)::
(makeTM BR1 DL0 CR1 DR1 AL1 EL0 AR1 CL0 HR1 BL0,RWL 2 3)::
(makeTM BR1 DL0 CR1 DR1 AL1 ER0 AL1 CL1 HR1 DR0,RWL 5 2)::
(makeTM BR1 DL0 CR1 DR1 DL1 HR1 ER0 AL0 AR1 AL1,RWL 4 3)::
(makeTM BR1 DL0 CR1 ER0 AL0 AL1 CL1 DR1 HR1 DR0,RWL 2 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 HR1 AL1 DL1 DR1 AR0,RWL 1 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 HR1 BL0 AL1 DR0 ER1,RWL 3 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 AL0 AL1 BR0 AR1 HR1,RWL 2 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 AR0 BR1 CL0 CL1 HR1,RWL 6 2)::
(makeTM BR1 DL0 CR1 ER0 AL1 AR0 DR1 CL0 BR0 HR1,RWL 6 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 CL1 HR1 AL1 BL1 CR0,RWL 2 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 CR1 CL0 BL0 AR0 HR1,RWL 3 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 EL0 HR1 CL0 BR1 ER1,RWL 7 2)::
(makeTM BR1 DL0 CR1 ER0 DL0 HR1 AL1 DL1 DR1 AR0,RWL 1 3)::
(makeTM BR1 DL0 CR1 ER0 DR0 HR1 AL1 DL1 DR1 AR0,RWL 1 3)::
(makeTM BR1 DL0 CR1 ER0 DL1 HR1 AL1 DL1 DR1 AR0,RWL 1 3)::
(makeTM BR1 DL0 CR1 ER0 DL1 AL1 HR1 CL1 AR1 ER1,RWL 8 2)::
(makeTM BR1 DL0 CR1 ER0 DR1 AR0 AL1 CL1 CR1 HR1,RWL 4 2)::
(makeTM BR1 DL0 CR1 ER0 DR1 AR1 EL1 BL1 HR1 AL0,RWL 1 4)::
(makeTM BR1 DL0 CR1 ER0 DR1 BR1 EL1 BL1 HR1 AL0,RWL 3 3)::
(makeTM BR1 DL0 CR1 ER0 DR1 BR1 EL1 CL0 HR1 AL0,RWL 3 3)::
(makeTM BR1 DL0 CR1 ER1 AL0 AR0 BL1 DL1 HR1 CR0,RWL 1 3)::
(makeTM BR1 DL0 CR1 ER1 AL1 DR0 CL1 BR0 HR1 AR1,RWL 3 2)::
(makeTM BR1 DL0 CR1 ER1 DL1 HR1 AL1 AL0 AR0 ER0,RWL 28 2)::
(makeTM BR1 DR0 BL1 CL1 AR1 CL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 DR0 BL1 CR1 EL0 DL1 HR1 CL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 DR0 CL0 HR1 AR1 CL1 EL1 DR1 CL1 CL0,RWL 2 3)::
(makeTM BR1 DR0 CL0 HR1 AR1 CL1 EL1 DR1 CR1 CL0,RWL 2 3)::
(makeTM BR1 DR0 CL0 HR1 DL1 CL1 AR1 ER0 CR0 AL0,RWL 10 2)::
(makeTM BR1 DR0 CL0 HR1 ER1 DL1 CR1 EL1 AR1 EL0,RWL 15 2)::
(makeTM BR1 DR0 CL0 AL0 DL0 CL1 AR1 EL0 CR0 HR1,RWL 5 2)::
(makeTM BR1 DR0 CL0 AR0 HR1 DL1 AR1 EL0 CL0 EL0,RWL 28 2)::
(makeTM BR1 DR0 CL0 AR1 HR1 AL1 ER0 DR1 EL1 BL0,RWL 2 3)::
(makeTM BR1 DR0 CL0 AR1 HR1 AL1 EL1 DR1 BL1 AL0,RWL 1 4)::
(makeTM BR1 DR0 CL0 AR1 AR0 BL1 DL1 ER1 HR1 CR0,RWL 7 2)::
(makeTM BR1 DR0 CL0 AR1 AR1 BL1 EL1 CR0 DL1 HR1,RWL 1 4)::
(makeTM BR1 DR0 CL0 AR1 BR1 CL1 HR1 ER1 CL0 ER1,RWL 2 2)::
(makeTM BR1 DR0 CL0 AR1 BR1 CL1 EL0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 DR0 CL0 AR1 BR1 CL1 EL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR0 CL0 AR1 BR1 CL1 EL0 DR1 HR1 CL1,RWL 2 2)::
(makeTM BR1 DR0 CL0 AR1 EL0 DL1 AL1 CL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 DR0 CL0 BR0 AR1 CL1 EL1 BL1 DL1 HR1,RWL 5 3)::
(makeTM BR1 DR0 CL0 BR0 CL1 DL1 ER1 BR1 HR1 AR1,RWL 2 3)::
(makeTM BR1 DR0 CL0 BR0 DL0 CL1 ER1 BR0 AR1 HR1,RWL 7 2)::
(makeTM BR1 DR0 CL0 BL1 DL1 AL1 AR1 EL1 AL0 HR1,RWL 4 3)::
(makeTM BR1 DR0 CL0 CR0 AR1 AL1 HR1 ER1 EL1 BL0,RWL 5 2)::
(makeTM BR1 DR0 CL0 CR0 AR1 AL1 EL1 DR1 HR1 BL0,RWL 5 2)::
(makeTM BR1 DR0 CL0 CR0 DL0 CL1 ER0 BR0 AR1 HR1,RWL 5 2)::
(makeTM BR1 DR0 CL0 CR0 EL1 DL1 AR1 BR1 BL0 HR1,RWL 8 3)::
(makeTM BR1 DR0 CL0 CR1 ER0 DL1 AL1 DL0 AR1 HR1,RWL 4 2)::
(makeTM BR1 DR0 CL0 DL0 DR1 BL1 AR1 EL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 DR0 CL0 DL1 CR1 AL1 HR1 ER0 EL1 BL1,RWL 5 2)::
(makeTM BR1 DR0 CL0 DL1 DR1 BL1 ER1 BL1 HR1 AR0,RWL 2 3)::
(makeTM BR1 DR0 CL0 DR1 AL1 CL1 HR1 ER0 BL1 CR0,RWL 2 3)::
(makeTM BR1 DR0 CL0 ER0 AL1 DL0 CL1 DL1 HR1 AR0,RWL 5 2)::
(makeTM BR1 DR0 CL0 ER0 DL1 CL1 BR1 AL0 HR1 AR1,RWL 4 3)::
(makeTM BR1 DR0 CL0 ER0 DR1 DL1 BL1 CL0 HR1 AR1,RWL 5 2)::
(makeTM BR1 DR0 CL0 ER1 AR0 DL1 BL1 AR1 HR1 AL1,RWL 5 2)::
(makeTM BR1 DR0 CL0 ER1 AR0 DL1 BL1 AR1 HR1 CR1,RWL 2 3)::
(makeTM BR1 DR0 CL0 ER1 AL1 DR1 CL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR0 CL0 ER1 AR1 DL1 BL1 AR1 HR1 CL1,RWL 2 3)::
(makeTM BR1 DR0 CL0 ER1 CR1 DL1 BL1 AR1 HR1 CL1,RWL 2 3)::
(makeTM BR1 DR0 CL0 ER1 DR1 DL1 BL1 AR1 HR1 AL1,RWL 5 2)::
(makeTM BR1 DR0 CR0 HR1 DL0 AR1 EL0 AR0 AL0 EL1,RWL 6 2)::
(makeTM BR1 DR0 CR0 HR1 DL0 AR1 ER1 EL0 CR1 EL1,RWL 4 3)::
(makeTM BR1 DR0 CR0 HR1 DL1 AR0 EL1 DL1 CR1 EL0,RWL 2 4)::
(makeTM BR1 DR0 CR0 AL0 DL1 AR1 EL0 HR1 BL1 BL0,RWL 14 2)::
(makeTM BR1 DR0 CR0 AR0 DL1 DR0 DL1 EL0 AL1 HR1,RWL 12 2)::
(makeTM BR1 DR0 CR0 AR1 CL1 DR1 HR1 EL0 BR1 AL1,RWL 5 2)::
(makeTM BR1 DR0 CR0 AR1 CL1 DR1 EL0 AL0 AL1 HR1,RWL 5 2)::
(makeTM BR1 DR0 CR0 AR1 DL1 HR1 EL0 DR1 BR1 EL1,RWL 2 2)::
(makeTM BR1 DR0 CR0 BL0 DL0 CR1 BL1 ER1 AR0 HR1,RWL 8 2)::
(makeTM BR1 DR0 CR0 BL0 DR1 EL1 CL1 AR1 BL0 HR1,RWL 6 2)::
(makeTM BR1 DR0 CR0 EL1 DL1 BR0 BL0 HR1 AL0 CL1,RWL 4 2)::
(makeTM BR1 DR0 CR0 ER1 CL0 DL1 AR1 DL0 BR0 HR1,RWL 5 2)::
(makeTM BR1 DR0 CR0 ER1 CL1 DL0 AL1 BL1 AR0 HR1,RWL 5 2)::
(makeTM BR1 DR0 CR0 ER1 CL1 DR1 HR1 EL0 BR1 AL1,RWL 4 2)::
(makeTM BR1 DR0 CL1 HR1 AL0 AR1 DL1 EL0 CR0 AL1,RWL 2 2)::
(makeTM BR1 DR0 CL1 HR1 AL0 AR1 DL1 EL0 CR0 EL1,RWL 2 3)::
(makeTM BR1 DR0 CL1 HR1 AR0 AR1 DL1 EL0 CL0 AL1,RWL 2 2)::
(makeTM BR1 DR0 CL1 HR1 DL0 CL0 EL1 ER0 AR1 CR0,RWL 12 2)::
(makeTM BR1 DR0 CL1 HR1 DL0 DL1 ER1 CL1 AR0 DL0,RWL 10 2)::
(makeTM BR1 DR0 CL1 HR1 DR1 DL0 ER0 EL0 CL0 AR1,RWL 3 2)::
(makeTM BR1 DR0 CL1 AL0 HR1 AR1 DL1 EL1 BR0 CL0,RWL 2 2)::
(makeTM BR1 DR0 CL1 AL0 AR1 BL0 ER1 HR1 CR0 AL0,RWL 12 2)::
(makeTM BR1 DR0 CL1 AL0 AR1 BL1 ER1 CR0 HR1 BL0,RWL 6 2)::
(makeTM BR1 DR0 CL1 AL0 DL1 BL1 AR1 EL0 AL0 HR1,RWL 11 2)::
(makeTM BR1 DR0 CL1 AR0 HR1 AL1 DL1 EL0 BR1 BL1,RWL 3 2)::
(makeTM BR1 DR0 CL1 AR0 AR0 BL1 DL1 EL0 AL1 HR1,RWL 3 3)::
(makeTM BR1 DR0 CL1 AR0 AL1 BL0 CR0 EL0 DL0 HR1,RWL 8 2)::
(makeTM BR1 DR0 CL1 AR0 AL1 BL0 ER1 CR1 HR1 AR1,RWL 2 4)::
(makeTM BR1 DR0 CL1 AR0 AL1 CL1 DL1 EL0 AL1 HR1,RWL 14 2)::
(makeTM BR1 DR0 CL1 AR0 AR1 BL1 CL0 EL0 DL1 HR1,RWL 8 2)::
(makeTM BR1 DR0 CL1 AR0 CR1 BL1 DL1 EL0 AL1 HR1,RWL 3 3)::
(makeTM BR1 DR0 CL1 AR0 DL0 BL1 ER0 AL1 CR1 HR1,RWL 2 2)::
(makeTM BR1 DR0 CL1 AR0 DR0 DL0 BL1 EL0 AL1 HR1,RWL 14 2)::
(makeTM BR1 DR0 CL1 AR0 DL1 BL1 EL0 AL1 AL1 HR1,RWL 2 2)::
(makeTM BR1 DR0 CL1 AR0 DR1 BL1 ER0 DL0 AL1 HR1,RWL 2 2)::
(makeTM BR1 DR0 CL1 AL1 AR1 DL0 ER1 BL0 CR0 HR1,RWL 14 2)::
(makeTM BR1 DR0 CL1 AL1 AR1 DL1 EL1 CR0 BL0 HR1,RWL 4 2)::
(makeTM BR1 DR0 CL1 AL1 EL0 AL1 HR1 CL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 DR0 CL1 AR1 HR1 DR0 AR1 EL1 DL0 CL0,RWL 6 2)::
(makeTM BR1 DR0 CL1 AR1 AL1 CL1 HR1 ER0 CL0 ER1,RWL 2 2)::
(makeTM BR1 DR0 CL1 AR1 BR1 AR1 DL1 ER0 HR1 BL0,RWL 4 2)::
(makeTM BR1 DR0 CL1 AR1 EL0 AL1 DL1 CL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 DR0 CL1 AR1 ER1 DL1 ER0 CL1 HR1 BL0,RWL 6 2)::
(makeTM BR1 DR0 CL1 BL0 HR1 DL0 ER1 BR1 AR1 DR0,RWL 7 2)::
(makeTM BR1 DR0 CL1 BL0 AR1 AL1 ER0 BL1 CR0 HR1,RWL 2 3)::
(makeTM BR1 DR0 CL1 BL0 AR1 BL0 ER1 HR1 AR0 CR0,RWL 4 2)::
(makeTM BR1 DR0 CL1 BR0 EL1 DL1 AR1 DL0 AL0 HR1,RWL 8 3)::
(makeTM BR1 DR0 CL1 BL1 AR1 DL1 ER0 BL0 HR1 CR1,RWL 14 2)::
(makeTM BR1 DR0 CL1 BL1 DR1 AL1 EL1 AR1 CL0 HR1,RWL 2 2)::
(makeTM BR1 DR0 CL1 BL1 DR1 BL0 ER0 AR1 HR1 AR1,RWL 35 2)::
(makeTM BR1 DR0 CL1 BL1 DR1 BL0 ER1 AR1 HR1 AL1,RWL 35 2)::
(makeTM BR1 DR0 CL1 BL1 DR1 CR1 EL0 AR1 HR1 BL0,RWL 2 2)::
(makeTM BR1 DR0 CL1 BL1 DR1 CR1 EL1 AR1 HR1 BL0,RWL 2 2)::
(makeTM BR1 DR0 CL1 BL1 DR1 CR1 EL1 AR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 DR0 CL1 BL1 DR1 CR1 EL1 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR0 CL1 BL1 DR1 CR1 EL1 AR1 HR1 DL0,RWL 2 2)::
(makeTM BR1 DR0 CL1 BR1 HR1 AL1 EL0 DL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 DR0 CL1 BR1 HR1 AL1 EL0 DR1 BL0 EL1,RWL 2 3)::
(makeTM BR1 DR0 CL1 BR1 HR1 AL1 EL0 DR1 CL1 EL1,RWL 2 3)::
(makeTM BR1 DR0 CL1 CL0 DR1 BL1 ER0 AR1 HR1 BR1,RWL 8 2)::
(makeTM BR1 DR0 CL1 CR0 HR1 DL0 EL1 BR1 AR1 DR0,RWL 2 3)::
(makeTM BR1 DR0 CL1 CR0 AR0 DL0 BL1 ER1 AR0 HR1,RWL 3 3)::
(makeTM BR1 DR0 CL1 CR0 DL1 CL1 AR1 ER0 HR1 CL0,RWL 9 3)::
(makeTM BR1 DR0 CL1 CL1 AR1 CL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 DR0 CL1 CR1 HR1 AL1 BL0 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 DR0 CL1 CR1 BR1 AR1 DL1 ER0 HR1 BL0,RWL 5 2)::
(makeTM BR1 DR0 CL1 DR0 HR1 AL1 BL0 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 DR0 CL1 DR0 HR1 DL0 AL1 ER0 AL0 CR1,RWL 2 3)::
(makeTM BR1 DR0 CL1 DR0 HR1 DL0 AL1 ER1 CL1 CR0,RWL 2 3)::
(makeTM BR1 DR0 CL1 DR0 BR1 AL1 HR1 ER0 EL1 CL0,RWL 3 2)::
(makeTM BR1 DR0 CL1 DL1 DR1 CL0 BL1 ER0 HR1 AR1,RWL 6 2)::
(makeTM BR1 DR0 CL1 DL1 EL0 BR1 HR1 CL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 DR0 CL1 EL0 AR0 BL0 AR1 HR1 AL0 CL1,RWL 4 2)::
(makeTM BR1 DR0 CL1 EL0 AR1 BL0 CL0 HR1 ER1 AR0,RWL 14 2)::
(makeTM BR1 DR0 CL1 EL0 AR1 BL0 CR0 HR1 BL0 DR0,RWL 11 2)::
(makeTM BR1 DR0 CL1 EL0 AR1 BL0 CR0 HR1 BR1 CL0,RWL 4 2)::
(makeTM BR1 DR0 CL1 EL0 AR1 BL0 ER0 HR1 BL0 CL0,RWL 3 4)::
(makeTM BR1 DR0 CL1 EL0 AR1 BL0 ER1 HR1 BR1 ER0,RWL 2 3)::
(makeTM BR1 DR0 CL1 EL0 AR1 BL1 HR1 CR0 BR1 CL1,RWL 7 2)::
(makeTM BR1 DR0 CL1 ER0 HR1 DR0 AR1 EL1 DL0 CL0,RWL 6 2)::
(makeTM BR1 DR0 CL1 ER0 HR1 DR0 BL0 AL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DR0 CL1 ER0 HR1 DR1 BL0 AL1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DR0 CL1 ER0 AR1 BL0 CR1 CL0 DR1 HR1,RWL 8 2)::
(makeTM BR1 DR0 CL1 ER0 AR1 BL1 HR1 BR0 CL0 EL1,RWL 4 3)::
(makeTM BR1 DR0 CL1 ER0 DL0 DL1 AR0 BL1 HR1 AR1,RWL 4 2)::
(makeTM BR1 DR0 CL1 ER0 DL1 BL1 BR1 AR1 HR1 CR0,RWL 2 2)::
(makeTM BR1 DR0 CL1 ER0 DL1 CL1 AL1 CR0 HR1 AR1,RWL 1 4)::
(makeTM BR1 DR0 CL1 EL1 AR0 BL0 AR1 HR1 CL0 EL0,RWL 4 2)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 AL1 HR1 CL0 ER0,RWL 3 3)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 CL0 HR1 AL0 ER0,RWL 5 3)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 CR0 HR1 BL0 AR1,RWL 4 2)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 CR0 HR1 BL0 CL0,RWL 4 2)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 CR0 HR1 DL1 AR1,RWL 4 2)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 CR0 HR1 DL1 CL0,RWL 4 2)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 CR1 HR1 CL0 ER0,RWL 12 3)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 ER0 HR1 CL0 ER0,RWL 3 3)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL0 ER1 HR1 CR0 ER1,RWL 5 3)::
(makeTM BR1 DR0 CL1 EL1 AR1 BL1 CR1 DL0 HR1 CR0,RWL 6 2)::
(makeTM BR1 DR0 CL1 ER1 AL1 DR1 CL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR0 CL1 ER1 AR1 BL1 AR1 CL1 HR1 CL0,RWL 3 3)::
(makeTM BR1 DR0 CL1 ER1 AR1 BL1 AR1 DL1 HR1 CL0,RWL 3 3)::
(makeTM BR1 DR0 CL1 ER1 DR0 BL0 AL0 AR1 AR0 HR1,RWL 14 2)::
(makeTM BR1 DR0 CL1 ER1 DR0 BL1 AR1 DL1 HR1 CL0,RWL 3 3)::
(makeTM BR1 DR0 CR1 HR1 AL0 AL1 BL1 ER0 EL1 CL0,RWL 3 2)::
(makeTM BR1 DR0 CR1 HR1 AL0 AL1 DL1 EL0 CR0 AL1,RWL 2 2)::
(makeTM BR1 DR0 CR1 HR1 AL0 AL1 ER0 BL0 EL1 CL0,RWL 3 2)::
(makeTM BR1 DR0 CR1 HR1 AL0 AL1 ER0 CL1 EL1 CL0,RWL 3 2)::
(makeTM BR1 DR0 CR1 HR1 AL0 AL1 ER0 DR1 EL1 CL0,RWL 3 2)::
(makeTM BR1 DR0 CR1 HR1 AL0 AL1 ER0 ER0 EL1 CL0,RWL 3 2)::
(makeTM BR1 DR0 CR1 HR1 AL0 AL1 ER1 CL0 DL1 ER1,RWL 2 4)::
(makeTM BR1 DR0 CR1 HR1 AL0 ER0 CL1 CL0 AL1 ER1,RWL 2 3)::
(makeTM BR1 DR0 CR1 HR1 AL1 AR0 AL0 EL1 DL1 AL1,RWL 3 2)::
(makeTM BR1 DR0 CR1 HR1 AL1 ER0 BL0 EL1 DR1 AL0,RWL 2 2)::
(makeTM BR1 DR0 CR1 HR1 DL0 AR0 EL0 DR1 AL0 EL1,RWL 2 2)::
(makeTM BR1 DR0 CR1 HR1 DL0 DL1 ER1 CL1 AR0 DL0,RWL 10 2)::
(makeTM BR1 DR0 CR1 HR1 DL1 AL0 ER1 DL1 AR1 EL0,RWL 2 4)::
(makeTM BR1 DR0 CR1 HR1 DL1 AR0 CR1 EL0 AL0 CL0,RWL 3 2)::
(makeTM BR1 DR0 CR1 HR1 DL1 CR0 AR1 EL0 DL0 CR1,RWL 6 2)::
(makeTM BR1 DR0 CR1 HR1 DL1 ER0 BL0 AL0 DL0 ER1,RWL 2 3)::
(makeTM BR1 DR0 CR1 AL0 BL1 ER0 BL0 DR1 HR1 DR1,RWL 2 3)::
(makeTM BR1 DR0 CR1 AL0 BL1 ER1 BL0 DR1 HR1 AL1,RWL 2 3)::
(makeTM BR1 DR0 CR1 AL0 BL1 ER1 BL0 DR1 HR1 AR1,RWL 2 3)::
(makeTM BR1 DR0 CR1 AR0 BL1 HR1 DL1 EL0 AL0 BL1,RWL 3 2)::
(makeTM BR1 DR0 CR1 AR0 DL0 CL1 ER0 CL0 AL1 HR1,RWL 6 4)::
(makeTM BR1 DR0 CR1 AR0 DL0 CL1 ER1 CL0 AR0 HR1,RWL 6 4)::
(makeTM BR1 DR0 CR1 AR0 DL1 HR1 EL0 DL1 AL1 AL0,RWL 4 2)::
(makeTM BR1 DR0 CR1 AR1 BL1 BL0 DL1 ER0 HR1 CL0,RWL 5 2)::
(makeTM BR1 DR0 CR1 AR1 BL1 BR1 DL1 ER0 HR1 CL0,RWL 5 2)::
(makeTM BR1 DR0 CR1 AR1 DL1 HR1 EL0 DL0 ER1 BR0,RWL 3 3)::
(makeTM BR1 DR0 CR1 AR1 DL1 CL1 ER0 CL0 HR1 AR1,RWL 7 2)::
(makeTM BR1 DR0 CR1 AR1 DL1 ER0 AL1 CL0 DR0 HR1,RWL 11 2)::
(makeTM BR1 DR0 CR1 BL0 DR1 CL1 EL0 AR0 HR1 BL1,RWL 4 2)::
(makeTM BR1 DR0 CR1 BR0 DL1 CL1 ER1 CL0 HR1 AR1,RWL 3 3)::
(makeTM BR1 DR0 CR1 BL1 BL1 AR1 HR1 ER1 BL0 ER1,RWL 2 2)::
(makeTM BR1 DR0 CR1 BL1 BL1 AR1 EL0 DR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 DR0 CR1 BL1 DL0 ER1 BL0 DR1 HR1 AR1,RWL 3 2)::
(makeTM BR1 DR0 CR1 BL1 DL1 AR1 HR1 ER1 BL0 ER1,RWL 2 2)::
(makeTM BR1 DR0 CR1 BL1 DL1 AR1 EL0 DR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 DR0 CR1 BL1 DL1 AR1 ER0 BL0 HR1 CR1,RWL 5 2)::
(makeTM BR1 DR0 CR1 BL1 DL1 ER1 BL0 DR1 HR1 AR1,RWL 3 2)::
(makeTM BR1 DR0 CR1 BL1 DR1 AR1 EL0 DR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 DR0 CR1 BL1 DR1 ER1 BL0 DR1 HR1 AR1,RWL 3 2)::
(makeTM BR1 DR0 CR1 BR1 AL1 CL1 EL1 DL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 DR0 CR1 BR1 AL1 CL1 EL1 DL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 DR0 CR1 DR0 CL1 AR0 DL1 EL0 BL1 HR1,RWL 4 2)::
(makeTM BR1 DR0 CR1 DL1 BL1 HR1 AR1 EL1 BL0 AL1,RWL 17 2)::
(makeTM BR1 DR0 CR1 DL1 BL1 DR0 ER1 AL0 HR1 DL0,RWL 2 3)::
(makeTM BR1 DR0 CR1 DL1 BL1 ER1 CL1 AL0 HR1 AR1,RWL 12 2)::
(makeTM BR1 DR0 CR1 DL1 DR1 HR1 EL1 ER0 AR1 BL0,RWL 2 3)::
(makeTM BR1 DR0 CR1 EL0 AL0 AR0 ER1 HR1 BL1 AL0,RWL 5 2)::
(makeTM BR1 DR0 CR1 EL0 DL1 ER0 BR1 EL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 DR0 CR1 ER0 DL0 AR0 BL1 DL1 HR1 DL0,RWL 4 2)::
(makeTM BR1 DR0 CR1 ER0 DL1 HR1 EL0 DL0 AL1 AR0,RWL 12 2)::
(makeTM BR1 DR0 CR1 EL1 AL1 ER0 BL0 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 DR0 CR1 EL1 DL1 HR1 ER1 DL1 AR1 BL0,RWL 12 2)::
(makeTM BR1 DR0 CR1 EL1 DR1 HR1 EL1 ER0 BL0 AR1,RWL 7 2)::
(makeTM BR1 DL1 BL0 CR0 DL1 DR1 AL1 EL0 HR1 BR1,RWL 3 2)::
(makeTM BR1 DL1 BL0 CR1 CL1 DR1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 BL0 CR1 DL1 ER0 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 BL1 CL0 DR1 CR0 ER1 AL0 HR1 BR0,RWL 2 3)::
(makeTM BR1 DL1 BL1 CR0 CL1 AL1 HR1 EL0 AL0 EL1,RWL 2 2)::
(makeTM BR1 DL1 BL1 CR0 CL1 AL1 HR1 EL0 AL1 EL1,RWL 2 2)::
(makeTM BR1 DL1 BL1 CR0 CL1 AL1 HR1 EL0 AR1 EL1,RWL 2 2)::
(makeTM BR1 DL1 BL1 CR0 CL1 AL1 HR1 EL1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 BL1 CR0 CL1 AL1 HR1 ER1 CL0 ER0,RWL 2 2)::
(makeTM BR1 DL1 BL1 CR0 CL1 AL1 HR1 ER1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 BL1 CR0 DR1 CL1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 BL1 CL1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 BL1 CL1 CR1 DR0 HR1 ER0 EL1 AL0,RWL 3 2)::
(makeTM BR1 DL1 BL1 CL1 DR1 ER0 HR1 CR0 EL1 AL0,RWL 3 2)::
(makeTM BR1 DL1 BL1 CR1 HR1 AL0 DR1 ER1 BR0 DL0,RWL 2 3)::
(makeTM BR1 DL1 BL1 CR1 HR1 DR1 EL1 ER0 AL1 AL0,RWL 2 3)::
(makeTM BR1 DL1 BL1 CR1 AL1 CR0 HR1 EL0 BL0 BR1,RWL 2 2)::
(makeTM BR1 DL1 BL1 CR1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 BL1 CR1 ER0 DL0 HR1 CR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CL0 HR1 HR1 DR1 CL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CL0 HR1 AL1 CR1 CR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CL0 HR1 AL1 CR1 EL1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CL0 HR1 AL1 CR1 ER1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CL0 HR1 EL1 DR1 CR1 ER0 HR1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CL0 AL0 HR1 DR1 ER1 BR0 BL1 DR1,RWL 3 2)::
(makeTM BR1 DL1 CL0 AL0 BL1 DR1 CR1 ER0 HR1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CL0 AR0 AL1 CL1 EL0 CL1 HR1 BR0,RWL 1 3)::
(makeTM BR1 DL1 CL0 AR0 AL1 CL1 EL0 CR1 HR1 BR0,RWL 1 3)::
(makeTM BR1 DL1 CL0 AR1 HR1 AL1 ER0 DL0 ER1 CL0,RWL 2 2)::
(makeTM BR1 DL1 CL0 AR1 BR1 CL1 ER1 AL0 HR1 DR1,RWL 6 2)::
(makeTM BR1 DL1 CL0 BR0 AR1 AL1 EL1 CR1 AL0 HR1,RWL 4 2)::
(makeTM BR1 DL1 CL0 BR0 AR1 AL1 EL1 DL1 AL0 HR1,RWL 4 2)::
(makeTM BR1 DL1 CL0 BR0 AR1 CL1 HR1 EL0 AL1 BL0,RWL 3 2)::
(makeTM BR1 DL1 CL0 BR1 DL1 CL1 ER1 EL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 DL1 CL0 CR0 HR1 DR1 AL1 ER0 BL1 EL0,RWL 3 3)::
(makeTM BR1 DL1 CL0 CR0 CL1 AL1 HR1 EL0 AL1 EL1,RWL 2 2)::
(makeTM BR1 DL1 CL0 CR0 CL1 AL1 HR1 EL0 AR1 EL1,RWL 2 2)::
(makeTM BR1 DL1 CL0 CR0 CL1 AL1 HR1 EL1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL0 CR0 CL1 AL1 HR1 ER1 CL0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL0 CR0 CL1 AL1 HR1 ER1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL0 DL0 CL1 AL1 HR1 ER1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL0 DR0 HR1 AL1 ER0 BL0 EL1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CL0 DR0 HR1 AL1 ER1 EL1 BR1 CL0,RWL 6 2)::
(makeTM BR1 DL1 CL0 DR1 HR1 DR1 BL1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CL0 DR1 BL1 CR1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CL0 DR1 CR1 DR0 AL1 ER0 HR1 BL0,RWL 3 2)::
(makeTM BR1 DL1 CL0 ER0 AR1 CL1 DR1 BL1 HR1 AR0,RWL 3 3)::
(makeTM BR1 DL1 CL0 ER0 AR1 CL1 ER0 BL1 HR1 AR0,RWL 3 3)::
(makeTM BR1 DL1 CL0 ER0 DL1 CR1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CL0 EL1 DL0 BL1 DR1 AR0 HR1 CL1,RWL 3 2)::
(makeTM BR1 DL1 CR0 HR1 CL1 AL0 BR0 ER1 EL1 DL0,RWL 2 3)::
(makeTM BR1 DL1 CR0 HR1 CL1 AL0 ER0 AL0 AR0 ER1,RWL 8 2)::
(makeTM BR1 DL1 CR0 HR1 CL1 AR1 AR1 EL0 BR1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CR0 HR1 CL1 DL0 ER0 AL1 AL0 CR0,RWL 2 3)::
(makeTM BR1 DL1 CR0 AL0 AL1 ER1 HR1 AL0 CR1 BL0,RWL 2 3)::
(makeTM BR1 DL1 CR0 AL0 AL1 ER1 HR1 AL0 CR1 DL0,RWL 2 3)::
(makeTM BR1 DL1 CR0 AL0 DL0 AR1 EL1 BR0 HR1 AL0,RWL 5 2)::
(makeTM BR1 DL1 CR0 AL0 DL0 AR1 EL1 ER0 HR1 AL0,RWL 5 2)::
(makeTM BR1 DL1 CR0 AR0 CL1 AR1 EL1 AL0 HR1 DL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 AL1 AL1 AR1 EL1 AL0 HR1 CL0,RWL 2 3)::
(makeTM BR1 DL1 CR0 AL1 CL1 AL0 HR1 EL0 BR0 AR1,RWL 2 3)::
(makeTM BR1 DL1 CR0 AL1 CL1 AL0 HR1 EL0 BR0 ER1,RWL 2 3)::
(makeTM BR1 DL1 CR0 AL1 DR1 HR1 EL1 ER0 CL0 BL0,RWL 2 3)::
(makeTM BR1 DL1 CR0 AR1 CL1 AR1 EL0 AL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL1 CR0 AR1 CL1 AR1 EL1 AL0 HR1 BL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 AR1 CL1 AR1 EL1 AL0 HR1 CL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 AR1 CL1 AR1 EL1 AL0 HR1 DL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 AR1 CL1 DR0 HR1 EL1 BR1 EL0,RWL 4 2)::
(makeTM BR1 DL1 CR0 AR1 DR1 ER0 BL1 DL0 AL1 HR1,RWL 4 3)::
(makeTM BR1 DL1 CR0 AR1 DR1 ER1 BL1 DL0 AR1 HR1,RWL 4 3)::
(makeTM BR1 DL1 CR0 BR0 CL1 AL0 HR1 ER1 BR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CR0 BR0 CL1 AL0 HR1 ER1 BL1 ER1,RWL 2 2)::
(makeTM BR1 DL1 CR0 BR0 CL1 AL0 EL0 AL1 BL1 HR1,RWL 2 3)::
(makeTM BR1 DL1 CR0 BR0 CL1 AL0 EL1 DR0 AL1 HR1,RWL 2 2)::
(makeTM BR1 DL1 CR0 BR0 CL1 AL0 EL1 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 DL1 CR0 BR0 DR0 ER1 EL1 HR1 AL0 AR0,RWL 7 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 HR1 EL1 AL0 BL0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 HR1 EL1 AL1 BL0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 HR1 EL1 BL0 BL0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 HR1 EL1 BL0 DR0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 HR1 EL1 BR0 BL0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 HR1 EL1 CR0 BL0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 HR1 EL1 CL1 BL0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 HR1 EL1 DR1 BL0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 BL1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 BR1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 CL1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 CR1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 EL0 BL0 BR1 HR1,RWL 2 2)::
(makeTM BR1 DL1 CR0 BL1 AL1 CR1 ER1 EL0 HR1 BL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 BL1 DL1 AR1 EL0 AL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 BL1 DL1 AR1 EL1 AL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 BL1 DR1 CR1 AL1 EL0 HR1 BL0,RWL 2 2)::
(makeTM BR1 DL1 CR0 BR1 CL1 AL0 HR1 EL0 BR0 EL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 BR1 CL1 AL1 HR1 ER0 BR0 DR0,RWL 6 2)::
(makeTM BR1 DL1 CR0 BR1 CL1 AL1 HR1 ER0 BR0 ER0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BR1 CL1 AL1 HR1 ER0 CL0 ER0,RWL 3 2)::
(makeTM BR1 DL1 CR0 BR1 CL1 AL1 ER0 DR0 CR0 HR1,RWL 3 2)::
(makeTM BR1 DL1 CR0 CL0 DR1 ER1 BL1 DL0 AR1 HR1,RWL 4 3)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL0 HR1 EL1 BR0 AR1,RWL 2 3)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL0 HR1 EL1 BR0 EL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL0 HR1 ER1 BR0 EL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL1 HR1 EL0 AL0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL1 HR1 EL0 AL1 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL1 HR1 EL0 AR1 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL1 HR1 EL0 BL1 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL1 HR1 EL1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL1 HR1 ER1 CL0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CR0 CR0 CL1 AL1 HR1 ER1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CR0 CR0 DR1 BL0 AL1 EL1 HR1 AR0,RWL 3 2)::
(makeTM BR1 DL1 CR0 CL1 AL1 AL0 BR0 ER0 HR1 DR1,RWL 2 3)::
(makeTM BR1 DL1 CR0 CL1 DL1 AL0 AL1 ER1 HR1 DR0,RWL 2 3)::
(makeTM BR1 DL1 CR0 DL0 CL1 AL1 HR1 ER1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CR0 DL0 DR1 HR1 ER1 BL0 AL1 DR0,RWL 5 2)::
(makeTM BR1 DL1 CR0 DR0 AL1 AL0 EL0 BR0 CL1 HR1,RWL 4 3)::
(makeTM BR1 DL1 CR0 DR1 DR0 EL0 AL1 CR1 HR1 BL0,RWL 10 2)::
(makeTM BR1 DL1 CR0 EL0 CL1 AL0 HR1 EL1 BR0 AR1,RWL 2 3)::
(makeTM BR1 DL1 CR0 EL0 CL1 AL0 HR1 EL1 BR0 EL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 EL0 CL1 AL0 HR1 ER1 BR0 EL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 EL0 CL1 AR1 EL0 AL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL1 CR0 ER0 CL1 AL0 HR1 AL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 DL1 CR0 ER0 CL1 AL0 BR0 DL1 HR1 AL0,RWL 2 3)::
(makeTM BR1 DL1 CR0 ER0 CL1 AL0 BR0 DL1 HR1 BL1,RWL 2 3)::
(makeTM BR1 DL1 CR0 ER0 CL1 AR1 BR1 DL0 HR1 DR0,RWL 16 2)::
(makeTM BR1 DL1 CR0 ER0 DL1 HR1 AL1 BL0 CL0 DR0,RWL 10 2)::
(makeTM BR1 DL1 CR0 ER1 CL1 AL0 BR0 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 DL1 CR0 ER1 CL1 AR1 BR1 DL0 HR1 AR0,RWL 6 3)::
(makeTM BR1 DL1 CR0 ER1 DR1 AL0 AL1 BL1 HR1 CR1,RWL 2 4)::
(makeTM BR1 DL1 CR0 ER1 DR1 CR1 AL1 AL0 HR1 DR0,RWL 2 4)::
(makeTM BR1 DL1 CL1 HR1 DR1 CL1 ER1 AL0 AR1 CR0,RWL 12 2)::
(makeTM BR1 DL1 CL1 AL0 HR1 AL1 DR1 ER0 CR1 BR1,RWL 2 3)::
(makeTM BR1 DL1 CL1 AL0 HR1 AR1 ER0 DR1 EL1 BL0,RWL 2 3)::
(makeTM BR1 DL1 CL1 AL0 AL1 AR0 ER1 EL0 HR1 BR0,RWL 3 2)::
(makeTM BR1 DL1 CL1 AL0 BL1 AR1 HR1 ER1 BR0 DL0,RWL 2 2)::
(makeTM BR1 DL1 CL1 AL0 DL0 AR1 BL1 ER1 HR1 CR0,RWL 5 2)::
(makeTM BR1 DL1 CL1 AL0 DR1 DL0 BL0 ER0 CR1 HR1,RWL 3 3)::
(makeTM BR1 DL1 CL1 AR0 HR1 AR1 CL0 EL1 AL1 AL0,RWL 6 2)::
(makeTM BR1 DL1 CL1 AR0 HR1 DR0 EL0 ER1 AL1 BL1,RWL 5 2)::
(makeTM BR1 DL1 CL1 AR0 AL1 BL1 EL0 CR0 HR1 AL1,RWL 7 2)::
(makeTM BR1 DL1 CL1 AR0 AL1 BL1 EL0 CL1 HR1 AL1,RWL 7 2)::
(makeTM BR1 DL1 CL1 AR0 AL1 BL1 EL0 EL1 HR1 AL1,RWL 4 2)::
(makeTM BR1 DL1 CL1 AR0 DR1 BL1 EL0 EL1 HR1 AL1,RWL 4 2)::
(makeTM BR1 DL1 CL1 AL1 DR1 BL0 HR1 ER0 AR1 BL0,RWL 4 2)::
(makeTM BR1 DL1 CL1 AR1 BR0 AL1 HR1 EL0 CR1 BL1,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR0 AL0 CR1 EL0 AL1 BL1 HR1,RWL 11 2)::
(makeTM BR1 DL1 CL1 BR0 CR1 AL1 EL0 HR1 EL1 BR1,RWL 2 3)::
(makeTM BR1 DL1 CL1 BR0 EL0 AR1 HR1 CL0 AL1 AR1,RWL 7 2)::
(makeTM BR1 DL1 CL1 BR0 EL1 AR1 HR1 CL0 DR1 DL0,RWL 1 4)::
(makeTM BR1 DL1 CL1 BR1 HR1 AL1 ER0 DL0 ER1 BL0,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR1 HR1 AL1 ER0 DL0 ER1 CL1,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR1 AL0 AL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 DL1 CL1 BR1 AL1 AL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 DL1 CL1 BR1 AL1 DR0 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 DL1 CL1 BR1 BR0 AL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 DL1 CL1 BR1 CL1 AL1 HR1 EL1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR1 CL1 AL1 HR1 ER1 BL0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR1 CL1 AL1 HR1 ER1 BR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR1 CL1 AL1 HR1 ER1 CL0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR1 CL1 AL1 HR1 ER1 CR0 ER0,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR1 CR1 AL1 HR1 EL1 CR0 EL0,RWL 2 2)::
(makeTM BR1 DL1 CL1 BR1 CR1 AL1 ER1 DL0 CR0 HR1,RWL 2 3)::
(makeTM BR1 DL1 CL1 BR1 DR1 AL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 DL1 CL1 BR1 ER0 AL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 DL1 CL1 CL0 ER1 AR0 BL0 HR1 CR1 AR1,RWL 5 2)::
(makeTM BR1 DL1 CL1 CL0 ER1 AR0 BL0 HR1 ER1 AR1,RWL 5 2)::
(makeTM BR1 DL1 CL1 CR0 HR1 AR1 AR1 EL1 DL0 AL1,RWL 3 3)::
(makeTM BR1 DL1 CL1 CR0 HR1 AR1 EL0 AL1 ER1 AL0,RWL 2 3)::
(makeTM BR1 DL1 CL1 CR0 AL0 AL1 HR1 EL0 BR0 EL1,RWL 3 2)::
(makeTM BR1 DL1 CL1 CR0 AR0 DR1 AL1 EL0 HR1 BR0,RWL 3 2)::
(makeTM BR1 DL1 CL1 CR0 AL1 AR1 HR1 EL0 ER1 CL0,RWL 3 2)::
(makeTM BR1 DL1 CL1 CL1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CL1 CL1 DR1 BR0 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CL1 CR1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CL1 DR0 HR1 AL1 BR0 ER0 EL1 AL0,RWL 1 3)::
(makeTM BR1 DL1 CL1 DR0 HR1 AL1 BL1 EL0 AR1 BR1,RWL 6 2)::
(makeTM BR1 DL1 CL1 DR0 HR1 AL1 CR0 ER0 EL1 AL0,RWL 1 3)::
(makeTM BR1 DL1 CL1 DR0 AL1 BL1 BL0 ER0 HR1 CR0,RWL 2 2)::
(makeTM BR1 DL1 CL1 DR0 AR1 AL1 EL0 CL0 AR0 HR1,RWL 6 3)::
(makeTM BR1 DL1 CL1 DR1 AL1 BR0 EL1 CR1 HR1 BL0,RWL 8 2)::
(makeTM BR1 DL1 CL1 DR1 AL1 CL0 BL1 EL0 HR1 AR0,RWL 6 2)::
(makeTM BR1 DL1 CL1 EL0 AR0 BL1 DR1 AR0 HR1 AL0,RWL 4 2)::
(makeTM BR1 DL1 CL1 EL0 AR1 BL1 DR1 AR0 HR1 AL0,RWL 4 2)::
(makeTM BR1 DL1 CL1 EL0 CR1 AR1 HR1 BL0 ER1 AR0,RWL 14 2)::
(makeTM BR1 DL1 CL1 EL0 DR1 BL1 DR1 AR0 HR1 AL0,RWL 4 2)::
(makeTM BR1 DL1 CL1 EL0 EL1 DL1 BL0 HR1 ER1 AR0,RWL 2 3)::
(makeTM BR1 DL1 CL1 ER0 HR1 AR0 AL1 BL0 AL0 DR1,RWL 3 2)::
(makeTM BR1 DL1 CL1 ER0 HR1 AR0 BR1 BL1 EL1 DL0,RWL 2 2)::
(makeTM BR1 DL1 CL1 ER0 HR1 AR0 BR1 CL1 EL1 DL0,RWL 2 2)::
(makeTM BR1 DL1 CL1 ER0 HR1 AR1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CL1 ER0 HR1 DL0 AL1 DR0 AR1 BL0,RWL 9 2)::
(makeTM BR1 DL1 CL1 ER0 HR1 DL0 EL0 BL0 AL1 ER1,RWL 16 2)::
(makeTM BR1 DL1 CL1 ER0 HR1 DR0 CR1 AL1 EL1 AL0,RWL 1 3)::
(makeTM BR1 DL1 CL1 ER0 HR1 DL1 DR1 BR0 EL1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CL1 ER0 AR0 AR1 HR1 CL0 EL1 AL0,RWL 2 3)::
(makeTM BR1 DL1 CL1 ER0 AR1 CL1 HR1 CL0 EL1 AL1,RWL 2 2)::
(makeTM BR1 DL1 CL1 ER0 DR0 CL0 BL1 DR1 HR1 AR1,RWL 3 3)::
(makeTM BR1 DL1 CL1 ER0 DR1 CL1 HR1 BR0 EL1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CL1 ER0 ER1 AR0 BL0 HR1 AL0 CR0,RWL 2 2)::
(makeTM BR1 DL1 CL1 EL1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CL1 ER1 AL0 AR0 AL1 ER0 HR1 BR0,RWL 2 3)::
(makeTM BR1 DL1 CL1 ER1 AL0 CR1 BR1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 DL1 CL1 ER1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 AL0 AL0 AR1 ER1 BL1 HR1 DR0,RWL 3 2)::
(makeTM BR1 DL1 CR1 AL0 AL1 AR1 ER1 BL1 HR1 DR0,RWL 3 2)::
(makeTM BR1 DL1 CR1 AL0 AL1 ER0 HR1 BR0 EL1 BL0,RWL 2 3)::
(makeTM BR1 DL1 CR1 AL0 CL1 AR1 ER1 BL1 HR1 DR0,RWL 3 2)::
(makeTM BR1 DL1 CR1 AL0 DL0 AR1 ER1 BL1 HR1 DR0,RWL 3 2)::
(makeTM BR1 DL1 CR1 AL0 DL1 AR1 ER1 BL1 HR1 DR0,RWL 3 2)::
(makeTM BR1 DL1 CR1 AL0 DL1 BR0 HR1 EL1 BL1 ER1,RWL 4 2)::
(makeTM BR1 DL1 CR1 AL0 DL1 ER0 DL1 BL1 HR1 AR1,RWL 7 2)::
(makeTM BR1 DL1 CR1 AL0 DL1 ER1 HR1 EL1 BL1 BR0,RWL 1 4)::
(makeTM BR1 DL1 CR1 AL0 DR1 HR1 ER1 BL0 BL1 CR0,RWL 9 2)::
(makeTM BR1 DL1 CR1 AR0 AL0 ER0 BR1 CL1 HR1 BL0,RWL 3 2)::
(makeTM BR1 DL1 CR1 AR0 AL0 ER1 BR1 CL1 HR1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CR1 AR0 AL1 AL0 EL0 CL1 HR1 AL1,RWL 12 2)::
(makeTM BR1 DL1 CR1 AR0 AL1 AR1 EL0 CL1 HR1 AL1,RWL 1 4)::
(makeTM BR1 DL1 CR1 AR0 AL1 BR1 EL0 CL1 HR1 AL1,RWL 3 2)::
(makeTM BR1 DL1 CR1 AR0 AL1 ER0 EL0 CL1 HR1 AL1,RWL 3 2)::
(makeTM BR1 DL1 CR1 AR0 BL1 ER0 AL0 BL0 DR0 HR1,RWL 6 2)::
(makeTM BR1 DL1 CR1 AR0 DL1 ER1 BR1 CL1 HR1 DL0,RWL 3 3)::
(makeTM BR1 DL1 CR1 AL1 DL1 ER0 AL0 BL1 HR1 BR1,RWL 3 3)::
(makeTM BR1 DL1 CR1 AL1 DR1 HR1 ER1 DL0 BL1 AR0,RWL 35 2)::
(makeTM BR1 DL1 CR1 AL1 DR1 ER0 AL0 BL1 HR1 BR1,RWL 3 3)::
(makeTM BR1 DL1 CR1 AR1 AL1 EL1 CL1 AL0 HR1 BR0,RWL 2 2)::
(makeTM BR1 DL1 CR1 AR1 DL0 BL1 HR1 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CR1 BL0 AL1 ER0 CR1 AL1 HR1 AR0,RWL 7 3)::
(makeTM BR1 DL1 CR1 BL0 DR0 ER0 DL1 BL1 HR1 AR1,RWL 15 2)::
(makeTM BR1 DL1 CR1 BL0 DR1 ER0 AL1 BL1 HR1 AR1,RWL 15 2)::
(makeTM BR1 DL1 CR1 BR0 AL0 ER1 CL1 DL1 HR1 BL1,RWL 3 3)::
(makeTM BR1 DL1 CR1 BR0 AL1 DR1 AR1 ER0 HR1 CL0,RWL 6 2)::
(makeTM BR1 DL1 CR1 BR0 DL1 AL0 EL1 BL1 AL1 HR1,RWL 5 2)::
(makeTM BR1 DL1 CR1 BR0 DL1 EL0 AL1 BL1 HR1 CL1,RWL 5 2)::
(makeTM BR1 DL1 CR1 BR0 DR1 ER0 DL0 AL1 HR1 BR0,RWL 7 2)::
(makeTM BR1 DL1 CR1 BR0 DR1 ER1 DL0 AL1 HR1 BL1,RWL 7 2)::
(makeTM BR1 DL1 CR1 BL1 AL0 ER0 HR1 AL1 BL0 ER1,RWL 2 2)::
(makeTM BR1 DL1 CR1 BL1 AL1 DR0 EL1 DR1 HR1 BL0,RWL 2 3)::
(makeTM BR1 DL1 CR1 BL1 DL1 ER0 HR1 BL0 AL0 ER1,RWL 6 3)::
(makeTM BR1 DL1 CR1 BR1 AL0 EL1 HR1 AL0 AL1 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL0 EL1 HR1 AL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL0 AR0 DL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL0 AL1 DL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL0 BR0 DL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL0 BL1 DL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL1 AL0 DL0,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL1 AL1 DL0,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL1 BR0 DL0,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL1 BL1 DL0,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 AL1 CL1 HR1 EL1 CR0 DL0,RWL 2 2)::
(makeTM BR1 DL1 CR1 BR1 DL1 CL1 AL1 EL0 HR1 AL1,RWL 3 2)::
(makeTM BR1 DL1 CR1 BR1 DL1 CL1 AL1 EL1 HR1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CR1 CR0 AL0 EL1 HR1 AL1 BL0 BR1,RWL 2 2)::
(makeTM BR1 DL1 CR1 CR0 AL0 EL1 HR1 AL1 BL0 DR0,RWL 2 2)::
(makeTM BR1 DL1 CR1 CR0 AL0 ER1 HR1 AL1 DL0 BL0,RWL 2 3)::
(makeTM BR1 DL1 CR1 CR0 AL0 ER1 HR1 AL1 DL0 CR1,RWL 2 3)::
(makeTM BR1 DL1 CR1 CL1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 CR1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 DL0 AL1 DR0 HR1 EL0 BR1 AR0,RWL 2 3)::
(makeTM BR1 DL1 CR1 DL0 AL1 DR0 HR1 EL0 BR1 ER0,RWL 2 3)::
(makeTM BR1 DL1 CR1 DR0 AL1 BL1 EL1 AR0 CL0 HR1,RWL 4 2)::
(makeTM BR1 DL1 CR1 DR0 AL1 CL1 ER0 CL0 HR1 AR1,RWL 14 2)::
(makeTM BR1 DL1 CR1 DR0 DL1 HR1 ER1 AL1 AR0 DL0,RWL 4 3)::
(makeTM BR1 DL1 CR1 DR1 DR0 HR1 AL1 ER0 BL0 EL0,RWL 6 2)::
(makeTM BR1 DL1 CR1 EL0 DL1 CR0 BL0 AL0 HR1 AR1,RWL 4 4)::
(makeTM BR1 DL1 CR1 EL0 DR1 HR1 AL1 ER0 CR0 BL0,RWL 5 2)::
(makeTM BR1 DL1 CR1 EL0 DR1 CR0 AL0 BR0 BL1 HR1,RWL 2 2)::
(makeTM BR1 DL1 CR1 ER0 AL0 AL1 HR1 BR1 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CR1 ER0 AL0 AL1 HR1 CR0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DL1 CR1 ER0 AL1 AR0 AL0 CL1 HR1 CR0,RWL 4 2)::
(makeTM BR1 DL1 CR1 ER0 AL1 BR0 AL0 CL0 DR0 HR1,RWL 57 2)::
(makeTM BR1 DL1 CR1 ER0 AL1 BR1 HR1 EL1 BR1 AL0,RWL 3 2)::
(makeTM BR1 DL1 CR1 ER0 AL1 CL0 HR1 EL1 AL0 AL1,RWL 3 2)::
(makeTM BR1 DL1 CR1 ER0 AL1 CL1 HR1 CL0 EL1 AL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 ER0 AL1 CL1 CL0 CR0 HR1 AR1,RWL 2 3)::
(makeTM BR1 DL1 CR1 ER0 DL0 AL1 AR1 CL0 DR1 HR1,RWL 3 2)::
(makeTM BR1 DL1 CR1 ER0 DL1 CR0 BL0 AL0 AR1 HR1,RWL 4 4)::
(makeTM BR1 DL1 CR1 EL1 AL0 BR0 BL1 CL1 CL0 HR1,RWL 3 3)::
(makeTM BR1 DL1 CR1 EL1 AL0 CR0 CL1 AL1 HR1 BL0,RWL 2 4)::
(makeTM BR1 DL1 CR1 EL1 AL1 CR0 CL1 BL0 HR1 AL0,RWL 3 3)::
(makeTM BR1 DL1 CR1 EL1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 EL1 AL1 EL0 HR1 AL1 BR1 CR0,RWL 2 2)::
(makeTM BR1 DL1 CR1 EL1 AL1 EL0 AL0 BL0 HR1 AR0,RWL 2 3)::
(makeTM BR1 DL1 CR1 ER1 AL0 HR1 AL1 BL0 BR0 DR0,RWL 2 2)::
(makeTM BR1 DL1 CR1 ER1 AL0 CR1 BR1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 DL1 CR1 ER1 AL1 AR0 CR1 DL0 HR1 DR0,RWL 11 2)::
(makeTM BR1 DL1 CR1 ER1 AL1 CR1 HR1 EL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 DL1 CR1 ER1 AL1 DR0 DL0 CL1 HR1 AR0,RWL 6 2)::
(makeTM BR1 DR1 BL1 CL0 CR1 DL0 CL0 ER0 AR1 HR1,RWL 16 3)::
(makeTM BR1 DR1 BL1 CR0 DL1 CL0 AR1 ER1 HR1 BR0,RWL 5 2)::
(makeTM BR1 DR1 BL1 CL1 AR0 ER0 HR1 AR1 BL0 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR0 ER0 HR1 AR1 BR0 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR0 ER1 HR1 AR1 BL0 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR0 ER1 HR1 AR1 BR0 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR0 ER1 HR1 AR1 BL1 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR1 AL0 ER0 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR1 ER1 HR1 AR1 BL1 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR1 ER1 HR1 BR0 BL0 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR1 ER1 HR1 BR0 BR0 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 AR1 ER1 HR1 CL0 BR0 ER0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CL1 DR1 EL0 HR1 CL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 DR1 BL1 CR1 HR1 AL1 CL0 ER0 EL1 AL0,RWL 2 2)::
(makeTM BR1 DR1 BL1 CR1 HR1 DR1 EL1 DR0 BL0 AL0,RWL 2 3)::
(makeTM BR1 DR1 CL0 HR1 DL1 CR1 EL1 AR0 CR0 EL0,RWL 4 3)::
(makeTM BR1 DR1 CL0 AL0 AR1 CL1 BR1 ER0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CL0 AL0 ER1 DL1 CL1 EL0 HR1 AR0,RWL 3 3)::
(makeTM BR1 DR1 CL0 AR1 HR1 AL1 ER0 AL0 BL1 DR0,RWL 5 2)::
(makeTM BR1 DR1 CL0 AR1 HR1 DL0 AL1 ER0 EL1 CR0,RWL 5 2)::
(makeTM BR1 DR1 CL0 AR1 AR0 BL1 EL1 ER0 HR1 CR0,RWL 6 2)::
(makeTM BR1 DR1 CL0 AR1 BR1 CL1 HR1 ER0 CL0 ER1,RWL 3 2)::
(makeTM BR1 DR1 CL0 AR1 BR1 CL1 CR0 EL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 DR1 CL0 AR1 DL0 CL1 AR0 EL0 HR1 BL1,RWL 7 2)::
(makeTM BR1 DR1 CL0 AR1 ER0 AL1 HR1 CR0 BL1 BL1,RWL 3 2)::
(makeTM BR1 DR1 CL0 AR1 ER0 AL1 HR1 CR0 BL1 CL0,RWL 3 2)::
(makeTM BR1 DR1 CL0 AR1 ER0 AL1 HR1 CR0 CL1 BL1,RWL 3 2)::
(makeTM BR1 DR1 CL0 BR0 DL0 CL1 ER1 BR0 AR1 HR1,RWL 8 4)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 AR1 ER1 HR1 BR0,RWL 3 2)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 BR0 ER1 HR1 AL0,RWL 3 2)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 BR0 ER1 HR1 BR0,RWL 3 2)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 BL1 ER0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 BR1 ER0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 CL1 ER0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 CR1 ER0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 DL1 ER1 HR1 BR0,RWL 3 2)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 ER0 BR0 BL1 HR1,RWL 2 3)::
(makeTM BR1 DR1 CL0 BR1 AR1 CL1 EL1 ER0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CL0 CR0 CL1 AL1 HR1 ER0 BL1 DR0,RWL 2 3)::
(makeTM BR1 DR1 CL0 CL1 HR1 DL1 CR1 EL0 ER1 AR0,RWL 2 3)::
(makeTM BR1 DR1 CL0 CL1 AR1 BL1 HR1 ER0 AL1 BR0,RWL 6 2)::
(makeTM BR1 DR1 CL0 CL1 ER1 DL1 CL1 EL0 HR1 AR0,RWL 3 3)::
(makeTM BR1 DR1 CL0 DL1 CR1 AL1 EL1 AR0 HR1 BL0,RWL 7 2)::
(makeTM BR1 DR1 CL0 EL0 DL1 CL1 AR1 BL0 HR1 DR0,RWL 4 4)::
(makeTM BR1 DR1 CL0 ER0 DL1 CL1 AR1 BL1 HR1 DR0,RWL 10 2)::
(makeTM BR1 DR1 CL0 ER1 AL1 DR0 CL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CL0 ER1 DL1 BL1 AR1 DR0 HR1 CL1,RWL 3 3)::
(makeTM BR1 DR1 CR0 HR1 CL1 DL0 ER1 EL0 AL1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CR0 HR1 DR0 DL0 EL1 AR1 AR1 EL0,RWL 5 3)::
(makeTM BR1 DR1 CR0 HR1 DL1 AR0 EL0 AR1 CR1 CL0,RWL 2 3)::
(makeTM BR1 DR1 CR0 HR1 DL1 AR1 ER1 DL0 AR1 EL1,RWL 3 2)::
(makeTM BR1 DR1 CR0 HR1 DL1 CR1 EL1 AR0 CR0 EL0,RWL 2 3)::
(makeTM BR1 DR1 CR0 HR1 DL1 CR1 EL1 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 DR1 CR0 HR1 DL1 DR0 EL1 ER1 AR0 CL0,RWL 5 2)::
(makeTM BR1 DR1 CR0 HR1 DR1 CR1 EL1 BR0 AL0 EL0,RWL 8 2)::
(makeTM BR1 DR1 CR0 AL0 DL1 CR1 BL1 EL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 DR1 CR0 AL0 DL1 ER1 BL1 BL0 HR1 CR1,RWL 2 3)::
(makeTM BR1 DR1 CR0 AR0 CL1 AL1 EL1 DL0 HR1 AL0,RWL 21 2)::
(makeTM BR1 DR1 CR0 AR1 CL1 DR0 HR1 EL0 AL1 BR1,RWL 5 2)::
(makeTM BR1 DR1 CR0 BR0 CL1 AL0 DL1 EL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 DR1 CR0 BR0 CL1 AL0 DL1 EL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CR0 BR0 CL1 AL0 EL1 BL1 HR1 DL1,RWL 2 2)::
(makeTM BR1 DR1 CR0 BR0 CL1 AL0 EL1 BR1 HR1 DL1,RWL 2 2)::
(makeTM BR1 DR1 CR0 BR0 CL1 AR1 HR1 ER1 BL1 EL0,RWL 2 4)::
(makeTM BR1 DR1 CR0 EL1 CL1 AL0 BL1 DL1 HR1 DL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 HR1 BL1 AR1 EL1 DR0 BL0 AL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 HR1 CL1 AR1 EL1 DR0 BL0 AL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 HR1 CL1 AR1 EL1 DR0 CL0 AL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 HR1 DL1 DR0 ER0 BL0 CR1 AR0,RWL 3 3)::
(makeTM BR1 DR1 CL1 HR1 EL1 DL1 ER1 CL0 AR1 DR0,RWL 10 3)::
(makeTM BR1 DR1 CL1 AL0 HR1 AR1 AL1 ER0 EL1 BL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 AL0 HR1 DL0 ER1 EL0 AR1 BL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 AL0 AR0 BL0 ER0 HR1 CR1 EL0,RWL 7 2)::
(makeTM BR1 DR1 CL1 AL0 AR0 BL0 ER1 HR1 CR0 CR1,RWL 8 2)::
(makeTM BR1 DR1 CL1 AL0 AR1 BL0 ER1 HR1 CR0 AR0,RWL 4 2)::
(makeTM BR1 DR1 CL1 AL0 DL0 CL0 ER1 BR0 AR0 HR1,RWL 3 2)::
(makeTM BR1 DR1 CL1 AL0 DR0 BL1 ER0 AR1 HR1 CR1,RWL 2 2)::
(makeTM BR1 DR1 CL1 AR0 AR1 BL0 EL1 HR1 CR1 ER1,RWL 4 4)::
(makeTM BR1 DR1 CL1 AR0 AR1 BL0 ER1 HR1 CR1 AL0,RWL 4 4)::
(makeTM BR1 DR1 CL1 AR0 AR1 BL0 ER1 HR1 CR1 ER1,RWL 4 4)::
(makeTM BR1 DR1 CL1 AL1 AR1 BL0 ER1 AR0 HR1 CR0,RWL 4 2)::
(makeTM BR1 DR1 CL1 AL1 AR1 BL0 ER1 AR0 HR1 CR1,RWL 4 2)::
(makeTM BR1 DR1 CL1 AR1 AR0 DL0 ER0 BL0 CL0 HR1,RWL 3 2)::
(makeTM BR1 DR1 CL1 AR1 AR1 DL0 ER1 BL0 CR0 HR1,RWL 3 2)::
(makeTM BR1 DR1 CL1 BL0 HR1 DL1 ER1 BL0 CL0 AR0,RWL 3 3)::
(makeTM BR1 DR1 CL1 BL0 AR0 BL0 ER1 HR1 CR1 ER0,RWL 4 4)::
(makeTM BR1 DR1 CL1 BL0 AR1 AL1 ER0 AR0 AR0 HR1,RWL 3 3)::
(makeTM BR1 DR1 CL1 BL0 EL1 DR0 HR1 BR0 AR1 DL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 BL1 HR1 DL1 ER1 AR0 AR1 EL0,RWL 2 2)::
(makeTM BR1 DR1 CL1 BL1 AR0 CL0 CR1 EL1 HR1 DL0,RWL 15 2)::
(makeTM BR1 DR1 CL1 BL1 DR0 CL0 AR1 ER1 HR1 CR0,RWL 4 3)::
(makeTM BR1 DR1 CL1 BL1 DR0 CR1 EL0 AR0 BL0 HR1,RWL 2 2)::
(makeTM BR1 DR1 CL1 BL1 DR0 CR1 EL1 AR0 BL1 HR1,RWL 2 2)::
(makeTM BR1 DR1 CL1 BL1 DR0 CR1 EL1 AR0 BR1 HR1,RWL 2 2)::
(makeTM BR1 DR1 CL1 BR1 HR1 AL1 EL0 DR0 EL1 BL0,RWL 2 2)::
(makeTM BR1 DR1 CL1 BR1 HR1 AL1 EL0 DR0 EL1 CL1,RWL 2 2)::
(makeTM BR1 DR1 CL1 BR1 HR1 AL1 ER0 DR0 EL1 BL0,RWL 2 2)::
(makeTM BR1 DR1 CL1 BR1 HR1 AL1 ER0 DR0 EL1 CL1,RWL 2 2)::
(makeTM BR1 DR1 CL1 BR1 EL0 AL1 EL1 AR0 HR1 CL1,RWL 2 3)::
(makeTM BR1 DR1 CL1 CL0 DL0 BL1 ER1 AR0 AR0 HR1,RWL 2 2)::
(makeTM BR1 DR1 CL1 CL0 DL0 BL1 ER1 AR0 AL1 HR1,RWL 2 2)::
(makeTM BR1 DR1 CL1 CL0 DR0 BL0 ER1 ER0 AR1 HR1,RWL 4 2)::
(makeTM BR1 DR1 CL1 CR0 AR0 DL0 BL1 ER0 CR1 HR1,RWL 8 2)::
(makeTM BR1 DR1 CL1 CR0 DR1 DL0 AR1 EL0 HR1 AL0,RWL 2 2)::
(makeTM BR1 DR1 CL1 DL0 EL1 DL1 BL1 AR0 AR1 HR1,RWL 10 3)::
(makeTM BR1 DR1 CL1 DL0 ER1 AL1 HR1 ER0 BL0 AR0,RWL 2 3)::
(makeTM BR1 DR1 CL1 DL1 AR0 BL0 AR1 ER0 HR1 DL0,RWL 1 4)::
(makeTM BR1 DR1 CL1 DL1 AL1 BL0 AR1 ER0 HR1 DL0,RWL 1 4)::
(makeTM BR1 DR1 CL1 DL1 BR1 BL0 ER0 AR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 DR1 CL1 DR1 DL0 BL1 AR0 EL0 HR1 AL1,RWL 8 2)::
(makeTM BR1 DR1 CL1 DR1 EL0 AL1 AR0 BR0 HR1 CL0,RWL 7 3)::
(makeTM BR1 DR1 CL1 EL0 HR1 DL0 ER1 BL0 AR1 AL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 EL0 AR1 BL0 AR0 HR1 CL1 CL1,RWL 6 2)::
(makeTM BR1 DR1 CL1 EL0 AR1 BL0 AR0 HR1 ER1 CL1,RWL 6 2)::
(makeTM BR1 DR1 CL1 EL0 AR1 BL0 BR1 HR1 ER1 AR0,RWL 14 2)::
(makeTM BR1 DR1 CL1 EL0 AR1 BL0 BR1 HR1 ER1 DR0,RWL 14 2)::
(makeTM BR1 DR1 CL1 EL0 AR1 BL0 ER0 HR1 AL0 CR0,RWL 12 2)::
(makeTM BR1 DR1 CL1 EL0 AR1 DL0 CR1 BL0 HR1 AL0,RWL 2 3)::
(makeTM BR1 DR1 CL1 EL0 DR1 CL1 HR1 BL0 ER1 AR0,RWL 3 2)::
(makeTM BR1 DR1 CL1 EL0 ER0 DL0 BL1 HR1 AR1 AR0,RWL 1 4)::
(makeTM BR1 DR1 CL1 ER0 DR0 CL0 BL1 DR1 HR1 AR1,RWL 3 3)::
(makeTM BR1 DR1 CL1 ER0 DL1 BL0 AR1 CR0 CR0 HR1,RWL 11 2)::
(makeTM BR1 DR1 CL1 EL1 HR1 DL0 ER1 BL0 AR1 CR0,RWL 1 4)::
(makeTM BR1 DR1 CL1 EL1 AR1 BL0 AR0 HR1 BR1 CR0,RWL 6 2)::
(makeTM BR1 DR1 CL1 EL1 AR1 BL0 AR0 HR1 CR0 BR0,RWL 6 2)::
(makeTM BR1 DR1 CL1 EL1 AR1 BL0 AR0 HR1 CR0 CR0,RWL 6 2)::
(makeTM BR1 DR1 CL1 EL1 AR1 BL0 CR1 HR1 CL0 ER0,RWL 6 2)::
(makeTM BR1 DR1 CL1 EL1 AR1 BL0 CR1 AR0 HR1 AL1,RWL 4 2)::
(makeTM BR1 DR1 CL1 EL1 AR1 BL0 ER0 HR1 BR1 CR0,RWL 8 2)::
(makeTM BR1 DR1 CL1 EL1 AR1 BL0 EL1 HR1 CL0 ER0,RWL 3 3)::
(makeTM BR1 DR1 CR1 HR1 DL0 ER1 AR0 CL0 DL1 AL0,RWL 4 3)::
(makeTM BR1 DR1 CR1 HR1 DL0 ER1 AR0 CL0 DL1 AR0,RWL 4 3)::
(makeTM BR1 DR1 CR1 HR1 DR0 AL1 BL1 ER0 EL1 CL0,RWL 2 2)::
(makeTM BR1 DR1 CR1 AR0 AL1 DL1 EL0 CL1 HR1 AL1,RWL 2 4)::
(makeTM BR1 DR1 CR1 AR0 CL1 DL1 EL0 AL0 HR1 AL1,RWL 3 3)::
(makeTM BR1 DR1 CR1 BL0 DR1 HR1 ER0 DR0 EL1 AL1,RWL 2 3)::
(makeTM BR1 DR1 CR1 BR0 DL0 AR1 HR1 ER0 EL1 BL1,RWL 3 2)::
(makeTM BR1 DR1 CR1 BL1 AL1 DR0 EL1 DR1 HR1 BL0,RWL 2 3)::
(makeTM BR1 DR1 CR1 BR1 AL0 ER1 DL1 CL0 AR0 HR1,RWL 9 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL0 AR1 DL1,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL0 BR1 DL1,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL0 CR0 DL1,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL0 CL1 DL1,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL1 AL0 DL0,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL1 AL1 DL0,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL1 BR0 DL0,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL1 BL1 DL0,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 HR1 EL1 CR0 DL0,RWL 2 2)::
(makeTM BR1 DR1 CR1 BR1 AL1 CL1 EL0 AL0 HR1 DL1,RWL 2 2)::
(makeTM BR1 DR1 CR1 CR0 AL0 ER1 DL1 CL0 AR0 HR1,RWL 9 2)::
(makeTM BR1 DR1 CR1 CL1 AL0 AR1 EL1 ER0 HR1 BR0,RWL 4 2)::
(makeTM BR1 DR1 CR1 DL0 BL1 AR0 ER0 CL0 CL1 HR1,RWL 3 2)::
(makeTM BR1 DR1 CR1 DR0 AL1 ER0 BL0 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 DR1 CR1 DR0 DL1 BR1 EL0 AL0 HR1 BL1,RWL 3 2)::
(makeTM BR1 DR1 CR1 EL0 DR1 AL0 BL1 AR0 HR1 CL1,RWL 3 3)::
(makeTM BR1 DR1 CR1 EL0 DR1 BL1 EL1 AR0 HR1 AL0,RWL 5 3)::
(makeTM BR1 DR1 CR1 ER0 AL1 AR0 BL1 DL1 HR1 DL0,RWL 7 2)::
(makeTM BR1 DR1 CR1 ER0 AL1 CL1 CL0 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CR1 ER0 DL1 AR0 BL1 DL1 HR1 DL0,RWL 7 2)::
(makeTM BR1 DR1 CR1 EL1 DL1 BR0 AR0 BL0 CL0 HR1,RWL 4 3)::
(makeTM BR1 DR1 CR1 EL1 DL1 BR0 ER1 CL0 HR1 AR1,RWL 4 2)::
(makeTM BR1 DR1 CR1 ER1 AL1 CL1 CL0 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 DR1 CR1 ER1 CL1 AL1 CL1 DR0 HR1 BR1,RWL 2 2)::
(makeTM BR1 DR1 CR1 ER1 DL1 CL0 AR0 CL0 CR0 HR1,RWL 4 3)::
(makeTM BR1 EL0 BL0 CR0 DR1 HR1 ER1 AR0 AL1 DL1,RWL 4 2)::
(makeTM BR1 EL0 BL0 CR1 BL1 DR0 DL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL0 BL0 CR1 BL1 DR0 DL1 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR1 EL0 BL0 CR1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 BL1 CL0 CR1 DR0 AL0 DR1 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL0 BL1 CL0 CR1 DR0 AL0 DR1 HR1 DR0,RWL 2 3)::
(makeTM BR1 EL0 BL1 CL0 DR0 CL1 AR1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL0 BL1 CR0 HR1 DL1 AL1 BR0 ER1 DR0,RWL 2 3)::
(makeTM BR1 EL0 BL1 CR0 HR1 DL1 AL1 BR1 ER1 DR0,RWL 2 3)::
(makeTM BR1 EL0 BL1 CR0 DR1 AL1 DL1 CL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 EL0 BL1 CL1 AL1 DR1 HR1 AL1 ER1 CR0,RWL 2 2)::
(makeTM BR1 EL0 BL1 CL1 AL1 DR1 HR1 BR0 ER1 CR0,RWL 2 3)::
(makeTM BR1 EL0 BL1 CL1 BR1 DR1 HR1 AL0 ER1 CR0,RWL 3 2)::
(makeTM BR1 EL0 BL1 CL1 DL0 CL0 DR1 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL0 BL1 CL1 DR0 CL0 DR1 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL0 BL1 CL1 DR1 AL0 BR0 AR1 HR1 DR1,RWL 3 2)::
(makeTM BR1 EL0 BL1 CR1 DR0 BL0 DL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL0 BL1 CR1 DR0 BL0 DL1 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR1 EL0 BL1 CR1 DR0 DR1 BR0 AL1 HR1 DL0,RWL 8 2)::
(makeTM BR1 EL0 CL0 AR1 DL0 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL0 AR1 DR0 CL1 AL1 DL0 HR1 CR0,RWL 3 3)::
(makeTM BR1 EL0 CL0 BR1 HR1 DR1 DL1 AL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL0 BR1 DL1 CR1 HR1 AL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL0 BR1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL0 BR1 DR1 CL1 HR1 AR1 BR0 ER1,RWL 2 2)::
(makeTM BR1 EL0 CL0 CR0 AR1 DR0 ER1 HR1 AL1 CL0,RWL 14 2)::
(makeTM BR1 EL0 CL0 CR0 DR0 AL1 BL1 AL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 EL0 CL0 CR0 DR0 AL1 DL1 AL0 HR1 BL1,RWL 3 2)::
(makeTM BR1 EL0 CL0 CR0 DR0 AL1 DL1 AL0 HR1 CR0,RWL 3 2)::
(makeTM BR1 EL0 CL0 CR0 DR1 AL1 DL1 CL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 EL0 CL0 CR0 ER1 DL1 BL1 HR1 AR0 BL0,RWL 7 2)::
(makeTM BR1 EL0 CL0 CL1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL0 CR1 AR0 DL1 AL1 BR0 CL1 HR1,RWL 5 2)::
(makeTM BR1 EL0 CL0 CR1 DL1 CR1 HR1 AL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL0 CR1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL0 DR0 AL1 CR0 DL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL0 CL0 DR0 AL1 CR0 DL1 AL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 EL0 CL0 DR0 AL1 CL1 HR1 ER1 BR1 AR0,RWL 4 3)::
(makeTM BR1 EL0 CL0 DR0 AL1 CL1 AR0 DR1 BL1 HR1,RWL 7 2)::
(makeTM BR1 EL0 CL0 DL1 HR1 AL1 AL1 CR1 ER1 DR0,RWL 2 2)::
(makeTM BR1 EL0 CL0 DL1 HR1 DR0 AL1 DR1 CR1 EL1,RWL 2 3)::
(makeTM BR1 EL0 CL0 DR1 HR1 DR0 AL1 DR1 CR1 EL1,RWL 2 3)::
(makeTM BR1 EL0 CL0 DR1 AL1 BL1 BR0 AR0 CL0 HR1,RWL 4 2)::
(makeTM BR1 EL0 CL0 DR1 AL1 BL1 BR0 BL0 DL1 HR1,RWL 4 2)::
(makeTM BR1 EL0 CL0 DR1 AR1 AL1 BR0 HR1 DR0 AL0,RWL 12 2)::
(makeTM BR1 EL0 CL0 DR1 AR1 DR0 ER1 HR1 AL1 CL0,RWL 14 2)::
(makeTM BR1 EL0 CL0 DR1 CR1 DR0 ER1 HR1 AL1 CL0,RWL 14 2)::
(makeTM BR1 EL0 CL0 DR1 DR0 BR0 ER1 HR1 AL1 CL0,RWL 9 2)::
(makeTM BR1 EL0 CL0 EL1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL0 ER1 DL1 CL0 AL1 ER0 HR1 CR0,RWL 2 3)::
(makeTM BR1 EL0 CL0 ER1 DL1 CR1 HR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 HR1 DL1 AR0 EL0 BR1 ER1 DL0,RWL 5 3)::
(makeTM BR1 EL0 CR0 HR1 DR1 AL0 DL1 CL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL0 CR0 HR1 DR1 AL0 EL1 AR0 CL1 EL1,RWL 2 4)::
(makeTM BR1 EL0 CR0 HR1 DR1 AL0 ER1 AR0 CL1 DL1,RWL 14 2)::
(makeTM BR1 EL0 CR0 HR1 DR1 AR1 AL0 DL1 DL1 CR0,RWL 3 2)::
(makeTM BR1 EL0 CR0 AR0 CL1 DL0 AR0 AL0 BR1 HR1,RWL 5 3)::
(makeTM BR1 EL0 CR0 AR0 CL1 DL0 AL1 HR1 BR0 AL1,RWL 6 3)::
(makeTM BR1 EL0 CR0 AR0 CL1 DL0 ER0 AL0 BR1 HR1,RWL 5 3)::
(makeTM BR1 EL0 CR0 AR0 CL1 DL1 AR1 HR1 BR0 AL1,RWL 6 3)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 AL1 AL1 BL1 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 AL1 AL1 CL0 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 AL1 BR0 BL1 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 AL1 BR0 CL0 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 AL1 CR0 BL1 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 AL1 CR0 CL0 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 CR1 AL1 BL1 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 CR1 AL1 CL0 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR0 AR0 DR0 AL1 DL1 CR1 BL1 HR1,RWL 4 3)::
(makeTM BR1 EL0 CR0 AR0 DR0 AL1 DL1 EL0 BL1 HR1,RWL 4 2)::
(makeTM BR1 EL0 CR0 AR0 DL1 CR0 EL1 HR1 AL1 DL0,RWL 2 3)::
(makeTM BR1 EL0 CR0 AL1 CL1 DR1 HR1 AL0 ER1 BR1,RWL 3 2)::
(makeTM BR1 EL0 CR0 AL1 DR0 HR1 DL1 BR0 AL0 BL0,RWL 24 2)::
(makeTM BR1 EL0 CR0 AR1 CL1 DL1 BR1 AL0 HR1 BR1,RWL 6 2)::
(makeTM BR1 EL0 CR0 AR1 DL0 ER1 BL1 HR1 AL1 CL0,RWL 2 2)::
(makeTM BR1 EL0 CR0 AR1 DL1 AR0 EL1 HR1 BL1 CL1,RWL 4 2)::
(makeTM BR1 EL0 CR0 BL0 DL1 AR0 AL0 AL1 CR1 HR1,RWL 6 2)::
(makeTM BR1 EL0 CR0 BL0 DR1 HR1 ER1 AR1 AL1 DR0,RWL 2 3)::
(makeTM BR1 EL0 CR0 BL0 DR1 HR1 ER1 ER0 AL1 DR0,RWL 2 3)::
(makeTM BR1 EL0 CR0 BR0 CL1 DL1 AR1 EL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BR0 DL1 DR0 AL0 AL1 DL1 HR1,RWL 12 2)::
(makeTM BR1 EL0 CR0 BL1 DL0 CR1 AL1 AR0 CL0 HR1,RWL 10 2)::
(makeTM BR1 EL0 CR0 BL1 DL0 CR1 DL1 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BL1 DL0 CR1 EL0 AR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BL1 DL1 CR1 BL1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BL1 DL1 CR1 BR1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BL1 DL1 CR1 CL1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BL1 DL1 CR1 CR1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BL1 DL1 CR1 DR0 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BL1 DL1 CR1 EL1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BL1 DL1 CR1 ER1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BR1 CL1 DL0 AL1 AL0 HR1 AR1,RWL 2 3)::
(makeTM BR1 EL0 CR0 BR1 CL1 DL0 AL1 AL0 HR1 DR0,RWL 2 3)::
(makeTM BR1 EL0 CR0 BR1 DL0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BR1 DR0 CR0 DL1 AL1 HR1 BL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BR1 DR0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL0 CR0 BR1 DL1 AR0 EL0 HR1 BL1 CL1,RWL 3 2)::
(makeTM BR1 EL0 CR0 BR1 DL1 AR1 AL0 HR1 CL1 CR0,RWL 3 3)::
(makeTM BR1 EL0 CR0 BR1 DR1 BR0 AL1 BL0 DL0 HR1,RWL 17 2)::
(makeTM BR1 EL0 CR0 CL0 DL1 AR1 AL0 HR1 CL1 CR0,RWL 3 3)::
(makeTM BR1 EL0 CR0 CL0 DR1 AL0 BL1 CL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL0 CR0 CL0 DR1 AL0 BL1 CL0 HR1 DR0,RWL 2 3)::
(makeTM BR1 EL0 CR0 CL0 DR1 AL0 BL1 EL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL0 CR0 CR0 CL1 DR0 HR1 ER1 AL1 EL1,RWL 2 3)::
(makeTM BR1 EL0 CR0 CR0 DR1 HR1 ER1 DR0 AL1 DL0,RWL 2 3)::
(makeTM BR1 EL0 CR0 CR0 DR1 AL1 DL1 CL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 EL0 CR0 CL1 AL1 DR0 BR0 CR1 BL0 HR1,RWL 7 3)::
(makeTM BR1 EL0 CR0 CL1 DL1 AR0 AL1 HR1 AR1 BL0,RWL 7 2)::
(makeTM BR1 EL0 CR0 DL0 CL1 AL1 HR1 BR1 DR0 EL1,RWL 3 3)::
(makeTM BR1 EL0 CR0 DL0 DR1 AR0 AL1 BL1 CL1 HR1,RWL 4 2)::
(makeTM BR1 EL0 CR0 DR0 AL1 HR1 CL1 AL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CR0 DR0 AL1 HR1 CL1 BL0 BR0 EL1,RWL 2 3)::
(makeTM BR1 EL0 CR0 DR0 AL1 HR1 CL1 ER1 AR0 BL0,RWL 17 2)::
(makeTM BR1 EL0 CR0 DR0 AL1 HR1 ER1 AR0 AL1 EL1,RWL 1 3)::
(makeTM BR1 EL0 CR0 DR0 AL1 AL0 CL1 DR1 HR1 DR0,RWL 2 3)::
(makeTM BR1 EL0 CR0 DR0 AL1 AL0 DL1 CL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL0 CR0 DR0 CL1 AL1 CR0 AL0 HR1 BL1,RWL 6 2)::
(makeTM BR1 EL0 CR0 DR0 DL0 HR1 ER1 AR0 AL1 EL1,RWL 1 3)::
(makeTM BR1 EL0 CR0 DR0 DR0 HR1 ER1 AR0 AL1 EL1,RWL 1 3)::
(makeTM BR1 EL0 CR0 DR0 DL1 HR1 ER1 AR0 AL1 EL1,RWL 1 3)::
(makeTM BR1 EL0 CR0 DR0 DR1 ER0 AL0 HR1 AL1 ER1,RWL 1 3)::
(makeTM BR1 EL0 CR0 DL1 CL1 BR0 AL0 HR1 DL1 CR0,RWL 5 3)::
(makeTM BR1 EL0 CR0 DL1 DR1 AL0 EL1 CL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL0 CR0 DR1 AL1 ER0 BL1 CR1 HR1 BL0,RWL 3 2)::
(makeTM BR1 EL0 CR0 DR1 BL1 DR0 ER1 HR1 AL1 CL0,RWL 9 2)::
(makeTM BR1 EL0 CR0 DR1 DR0 BR0 AL1 CL0 HR1 CL0,RWL 3 3)::
(makeTM BR1 EL0 CR0 EL0 CL1 DL0 AL1 AL0 HR1 AR1,RWL 2 3)::
(makeTM BR1 EL0 CR0 EL0 DR1 HR1 AL1 AR1 DL1 CR0,RWL 5 2)::
(makeTM BR1 EL0 CR0 ER0 DL0 ER1 CL0 HR1 AL1 BL1,RWL 9 2)::
(makeTM BR1 EL0 CR0 ER0 DR0 CL0 ER1 HR1 AL1 BL1,RWL 9 2)::
(makeTM BR1 EL0 CR0 ER0 DR0 DR0 ER1 HR1 AL1 CL0,RWL 9 2)::
(makeTM BR1 EL0 CR0 ER0 DL1 ER1 CL1 HR1 AL1 BL1,RWL 9 2)::
(makeTM BR1 EL0 CR0 ER0 DR1 ER1 AL0 HR1 AL1 BL1,RWL 9 2)::
(makeTM BR1 EL0 CR0 ER0 DR1 ER1 BL1 HR1 AL1 BL1,RWL 9 2)::
(makeTM BR1 EL0 CR0 ER0 DR1 ER1 CL1 HR1 AL1 BL1,RWL 9 2)::
(makeTM BR1 EL0 CR0 ER0 DR1 ER1 EL1 HR1 AL1 BL1,RWL 9 2)::
(makeTM BR1 EL0 CR0 EL1 CL1 DL0 AL1 AL0 HR1 AR1,RWL 2 3)::
(makeTM BR1 EL0 CR0 EL1 DL1 BR0 CL1 HR1 AL0 CL0,RWL 10 2)::
(makeTM BR1 EL0 CR0 EL1 DL1 BR0 CL1 HR1 AL0 ER0,RWL 2 3)::
(makeTM BR1 EL0 CR0 EL1 DL1 BR0 CL1 HR1 AL0 EL1,RWL 2 3)::
(makeTM BR1 EL0 CR0 ER1 DL0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL0 CR0 ER1 DR0 CR0 DL1 AL1 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL0 CR0 ER1 DL1 AR0 AL0 HR1 CR0 CL1,RWL 4 2)::
(makeTM BR1 EL0 CR0 ER1 DL1 AR1 AL1 HR1 CL0 AL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 HR1 AL0 DR1 HR1 AL1 ER1 CR0,RWL 2 2)::
(makeTM BR1 EL0 CL1 HR1 DL1 CR1 CR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 HR1 DL1 CR1 EL1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 HR1 DL1 CR1 ER1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 HR1 DL1 DR0 AL1 DR1 CR1 EL1,RWL 2 3)::
(makeTM BR1 EL0 CL1 HR1 DR1 CR1 AL0 DL1 AL0 AL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 HR1 DR1 CR1 AL0 DL1 CR0 AL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 HR1 DR1 CR1 AL0 DL1 CL1 AL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 HR1 DR1 DR0 AL1 DR1 CR1 EL1,RWL 2 3)::
(makeTM BR1 EL0 CL1 AL0 HR1 DL1 AR1 CL1 DR1 AR0,RWL 2 3)::
(makeTM BR1 EL0 CL1 AL0 HR1 DL1 BR1 CR0 ER1 DR0,RWL 3 2)::
(makeTM BR1 EL0 CL1 AL0 HR1 DL1 ER1 CL1 AR1 AR0,RWL 2 3)::
(makeTM BR1 EL0 CL1 AR0 HR1 DL1 AR1 BL1 DR0 AL1,RWL 3 3)::
(makeTM BR1 EL0 CL1 AR0 HR1 DL1 CR1 EL1 AL1 BL1,RWL 4 2)::
(makeTM BR1 EL0 CL1 AR0 HR1 DL1 EL1 HR1 AL1 BL1,RWL 4 2)::
(makeTM BR1 EL0 CL1 AR0 HR1 DL1 EL1 BL1 AL1 AL0,RWL 6 2)::
(makeTM BR1 EL0 CL1 AR0 HR1 DL1 EL1 BL1 AL1 CR1,RWL 4 2)::
(makeTM BR1 EL0 CL1 AR0 HR1 DR1 EL1 DL1 AL1 BL1,RWL 4 2)::
(makeTM BR1 EL0 CL1 AR0 AR0 DL1 BL1 HR1 AL1 BL1,RWL 2 3)::
(makeTM BR1 EL0 CL1 AR0 AL1 DL0 BL0 BL1 AR1 HR1,RWL 4 2)::
(makeTM BR1 EL0 CL1 AR0 AL1 DL0 BL1 BR0 DL1 HR1,RWL 8 2)::
(makeTM BR1 EL0 CL1 AR0 AL1 DL0 CL1 HR1 ER1 BR0,RWL 4 3)::
(makeTM BR1 EL0 CL1 AR0 DL0 DR1 AL1 BR0 DL0 HR1,RWL 5 3)::
(makeTM BR1 EL0 CL1 AR0 DL1 CL0 BR0 AL0 DR1 HR1,RWL 18 2)::
(makeTM BR1 EL0 CL1 AR0 DL1 CR0 EL1 HR1 AL1 BL0,RWL 4 2)::
(makeTM BR1 EL0 CL1 AR0 DL1 CR0 EL1 HR1 AL1 DL0,RWL 4 2)::
(makeTM BR1 EL0 CL1 AR0 EL0 DL1 BL1 HR1 AL1 BL1,RWL 2 3)::
(makeTM BR1 EL0 CL1 AR0 EL1 DL0 CR1 HR1 AL1 BL1,RWL 2 3)::
(makeTM BR1 EL0 CL1 AR0 EL1 DL1 BL1 HR1 AL1 BL1,RWL 2 3)::
(makeTM BR1 EL0 CL1 AR0 ER1 DL1 BL1 HR1 AL1 BL1,RWL 2 3)::
(makeTM BR1 EL0 CL1 AL1 AL0 DR0 HR1 AL1 ER1 CR0,RWL 2 2)::
(makeTM BR1 EL0 CL1 AL1 DR0 BL1 HR1 AR0 ER1 DL0,RWL 5 2)::
(makeTM BR1 EL0 CL1 AL1 DR1 BL1 HR1 AR0 ER1 DL0,RWL 5 2)::
(makeTM BR1 EL0 CL1 AR1 HR1 DL1 CR1 AR0 AL1 DR0,RWL 3 3)::
(makeTM BR1 EL0 CL1 AR1 AL0 DR0 EL1 DR1 HR1 BL0,RWL 7 2)::
(makeTM BR1 EL0 CL1 AR1 DL0 CR0 ER1 HR1 AL1 CL0,RWL 2 2)::
(makeTM BR1 EL0 CL1 AR1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL0 CL1 AR1 DR1 CL1 HR1 BR0 CR0 AL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 BL0 AL0 DR1 HR1 BR0 ER1 CR0,RWL 3 2)::
(makeTM BR1 EL0 CL1 BL0 DR1 BR0 AL1 CR0 BL1 HR1,RWL 2 3)::
(makeTM BR1 EL0 CL1 BR0 AR1 DL0 AL1 HR1 BL0 AR0,RWL 3 3)::
(makeTM BR1 EL0 CL1 BR0 CR1 DL0 AL1 AR0 BL0 HR1,RWL 6 2)::
(makeTM BR1 EL0 CL1 BR0 DL0 CL1 ER1 AL0 AR0 HR1,RWL 12 2)::
(makeTM BR1 EL0 CL1 BR0 DR0 DL0 AL1 BR1 BL0 HR1,RWL 6 2)::
(makeTM BR1 EL0 CL1 BR0 DL1 AL1 CR1 HR1 EL1 BR1,RWL 2 2)::
(makeTM BR1 EL0 CL1 BR0 DR1 BL1 AL1 CR1 HR1 DL0,RWL 4 3)::
(makeTM BR1 EL0 CL1 BR0 ER0 DL0 AL1 HR1 BL0 BR1,RWL 3 3)::
(makeTM BR1 EL0 CL1 BR0 EL1 DL0 BL1 HR1 AR0 CL0,RWL 3 2)::
(makeTM BR1 EL0 CL1 BL1 DR1 BL0 AR1 DR0 HR1 AL1,RWL 8 3)::
(makeTM BR1 EL0 CL1 BR1 HR1 DL0 AR1 DL1 BR0 ER1,RWL 2 3)::
(makeTM BR1 EL0 CL1 BR1 HR1 DR0 AL1 DL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 BR1 HR1 DL1 AL1 AL1 BR0 EL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 BR1 HR1 DL1 AL1 CR0 BR0 EL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 BR1 HR1 DL1 BR0 AL1 BR0 EL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 BR1 HR1 DL1 BR0 AL1 CR0 EL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 BR1 HR1 DL1 BR0 AL1 DR1 EL1,RWL 1 3)::
(makeTM BR1 EL0 CL1 BR1 HR1 DL1 CR1 AL1 BR0 EL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 BR1 HR1 DL1 ER0 AL1 BR0 EL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 CR0 HR1 DR0 AL1 DR1 ER1 DL1,RWL 3 4)::
(makeTM BR1 EL0 CL1 CR0 AR0 DL0 EL1 HR1 AL1 EL0,RWL 3 3)::
(makeTM BR1 EL0 CL1 CR0 AR0 DL1 CL1 HR1 AL1 EL0,RWL 5 3)::
(makeTM BR1 EL0 CL1 CR0 AR0 DL1 EL1 HR1 AL1 BL0,RWL 1 4)::
(makeTM BR1 EL0 CL1 CR0 AR0 DR1 HR1 ER1 AL1 BL0,RWL 11 3)::
(makeTM BR1 EL0 CL1 CR0 BL1 DL1 ER1 AL1 HR1 BR1,RWL 6 2)::
(makeTM BR1 EL0 CL1 CR0 CL1 DL1 ER1 AL1 HR1 BR1,RWL 6 2)::
(makeTM BR1 EL0 CL1 CR0 DL0 CR1 ER1 DL1 HR1 AR1,RWL 3 2)::
(makeTM BR1 EL0 CL1 CR0 DR1 CL1 HR1 ER1 BR1 AL1,RWL 20 2)::
(makeTM BR1 EL0 CL1 CL1 AL0 DR1 HR1 BR0 ER1 CR0,RWL 3 2)::
(makeTM BR1 EL0 CL1 CL1 AL1 DR1 HR1 AL1 ER1 CR0,RWL 2 2)::
(makeTM BR1 EL0 CL1 CR1 DR0 DL0 BL1 AR0 AL1 HR1,RWL 3 3)::
(makeTM BR1 EL0 CL1 CR1 DL1 CR0 AL1 BL0 HR1 DL0,RWL 16 3)::
(makeTM BR1 EL0 CL1 CR1 DL1 CR0 AL1 DL1 HR1 BL0,RWL 8 3)::
(makeTM BR1 EL0 CL1 DL0 HR1 AL1 AR0 AR1 BR0 EL1,RWL 2 3)::
(makeTM BR1 EL0 CL1 DL0 DL0 BL0 AR0 ER0 DR1 HR1,RWL 4 2)::
(makeTM BR1 EL0 CL1 DR0 HR1 AL1 AL0 AL1 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 DR0 HR1 BR1 DL1 AL1 CR0 EL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 DR0 AL1 BR1 CR1 CR0 BL0 HR1,RWL 11 2)::
(makeTM BR1 EL0 CL1 DR0 AL1 CL0 AR0 HR1 AR1 DR1,RWL 28 2)::
(makeTM BR1 EL0 CL1 DR0 AL1 CL1 HR1 AR1 AL0 BR0,RWL 1 4)::
(makeTM BR1 EL0 CL1 DR0 AR1 AL1 AR1 DR1 HR1 BL1,RWL 6 3)::
(makeTM BR1 EL0 CL1 DL1 HR1 AL1 CL1 DR1 DR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 DL1 AL1 DL0 CR0 ER1 HR1 BR0,RWL 2 2)::
(makeTM BR1 EL0 CL1 DL1 DR1 BL0 AL0 AR1 HR1 AR0,RWL 29 2)::
(makeTM BR1 EL0 CL1 DL1 DR1 BL0 AL1 AR1 HR1 AR0,RWL 9 2)::
(makeTM BR1 EL0 CL1 DL1 DR1 BL0 ER0 AR1 HR1 AR0,RWL 4 2)::
(makeTM BR1 EL0 CL1 DL1 DR1 BL0 ER1 AR1 HR1 AR0,RWL 14 2)::
(makeTM BR1 EL0 CL1 DR1 HR1 AL1 CL1 DR1 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 DR1 HR1 AL1 CL1 DR1 DR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CL1 DR1 AL1 BL0 AR1 AR0 HR1 BL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 DR1 AL1 BR1 BR0 CR1 HR1 CL1,RWL 3 3)::
(makeTM BR1 EL0 CL1 DR1 AL1 CR0 AL1 BR1 HR1 BL0,RWL 7 3)::
(makeTM BR1 EL0 CL1 DR1 CR1 BL1 HR1 AL1 ER1 BR0,RWL 2 2)::
(makeTM BR1 EL0 CL1 DR1 CR1 DL0 CL0 ER1 AR0 HR1,RWL 4 2)::
(makeTM BR1 EL0 CL1 DR1 DR0 BL0 AR1 AR0 HR1 BL1,RWL 3 2)::
(makeTM BR1 EL0 CL1 EL0 DL1 BL0 EL0 HR1 ER1 AR0,RWL 3 3)::
(makeTM BR1 EL0 CL1 ER0 HR1 DL1 AL1 BL1 AR1 DL0,RWL 3 2)::
(makeTM BR1 EL0 CL1 ER0 DL1 CL1 AR1 DR1 HR1 AR1,RWL 3 2)::
(makeTM BR1 EL0 CL1 ER1 DL1 BL0 AL1 HR1 AR0 AR1,RWL 2 4)::
(makeTM BR1 EL0 CL1 ER1 DL1 BL0 BR1 HR1 AR0 AR1,RWL 6 2)::
(makeTM BR1 EL0 CL1 ER1 DR1 BL0 HR1 AR1 AR0 CR1,RWL 4 2)::
(makeTM BR1 EL0 CR1 HR1 DL1 CR1 CR1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 HR1 DL1 CR1 EL1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 HR1 DL1 CR1 ER1 AL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 HR1 DL1 DR0 AL1 DR1 CR1 EL1,RWL 2 3)::
(makeTM BR1 EL0 CR1 HR1 DR1 AL0 AL1 BR0 AR1 CL1,RWL 9 3)::
(makeTM BR1 EL0 CR1 HR1 DR1 AR1 AL0 DR0 DL0 EL1,RWL 15 2)::
(makeTM BR1 EL0 CR1 HR1 DR1 AR1 AL0 EL1 DL1 CR0,RWL 4 2)::
(makeTM BR1 EL0 CR1 HR1 DR1 CR1 AL0 DL1 AL0 AL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 HR1 DR1 CR1 AL0 DL1 BL1 AL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 HR1 DR1 CR1 AL0 DL1 CR0 AL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 HR1 DR1 CR1 AL0 DL1 CL1 AL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 HR1 DR1 CR1 AL1 CR0 CL1 DL0,RWL 1 3)::
(makeTM BR1 EL0 CR1 HR1 DR1 DR0 AL1 DR1 CR1 EL1,RWL 2 3)::
(makeTM BR1 EL0 CR1 AL0 DL1 BR0 BL1 DL1 HR1 BR0,RWL 3 2)::
(makeTM BR1 EL0 CR1 AR0 CL1 DL0 AR1 BL0 DL1 HR1,RWL 2 3)::
(makeTM BR1 EL0 CR1 AR0 DL0 AL0 AR1 CL1 HR1 BR0,RWL 2 2)::
(makeTM BR1 EL0 CR1 AR0 DR0 AR1 ER1 HR1 AL1 EL0,RWL 2 3)::
(makeTM BR1 EL0 CR1 AR0 DL1 BL0 AL1 CL1 BL0 HR1,RWL 11 2)::
(makeTM BR1 EL0 CR1 AR0 DR1 HR1 AL1 BR1 DL1 AL0,RWL 7 2)::
(makeTM BR1 EL0 CR1 AR0 DR1 HR1 AL1 DR0 AL0 DR1,RWL 6 2)::
(makeTM BR1 EL0 CR1 AL1 DR0 HR1 AL1 DR1 AL0 CR0,RWL 4 2)::
(makeTM BR1 EL0 CR1 AL1 DR0 HR1 DL1 BR1 CR1 BL0,RWL 3 2)::
(makeTM BR1 EL0 CR1 AL1 DR0 CR1 ER1 HR1 BL0 AR0,RWL 6 2)::
(makeTM BR1 EL0 CR1 AL1 DR1 AR1 BL1 CR0 HR1 CL1,RWL 29 2)::
(makeTM BR1 EL0 CR1 AR1 DL0 BR0 HR1 EL1 DL0 BL1,RWL 2 3)::
(makeTM BR1 EL0 CR1 BL0 CL1 DR1 AL1 CR0 DL1 HR1,RWL 4 2)::
(makeTM BR1 EL0 CR1 BL0 DL1 CR0 AL0 BL1 HR1 CR1,RWL 7 4)::
(makeTM BR1 EL0 CR1 BL0 DR1 HR1 ER1 AR0 AL1 DR0,RWL 4 2)::
(makeTM BR1 EL0 CR1 BL0 DR1 HR1 ER1 CR0 AL1 DR0,RWL 4 2)::
(makeTM BR1 EL0 CR1 BR0 DL0 AR0 AR1 CL1 AL1 HR1,RWL 2 2)::
(makeTM BR1 EL0 CR1 BR0 DL0 BR1 AL0 DL1 HR1 BL0,RWL 15 2)::
(makeTM BR1 EL0 CR1 BR0 DL1 AR0 AL0 CL0 BR0 HR1,RWL 4 2)::
(makeTM BR1 EL0 CR1 BL1 BL1 DR0 AL1 DR1 HR1 BL1,RWL 2 3)::
(makeTM BR1 EL0 CR1 BL1 CL0 DR0 AL1 DR1 HR1 BL1,RWL 2 3)::
(makeTM BR1 EL0 CR1 BR1 DL0 CL1 AR1 EL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 BR1 DL1 DR0 HR1 AL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 BR1 DR1 BR0 AL1 BL0 HR1 DL0,RWL 7 2)::
(makeTM BR1 EL0 CR1 BR1 DR1 CL1 EL1 EL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL0 CR1 BR1 DR1 ER1 AL1 BL0 HR1 DL0,RWL 3 2)::
(makeTM BR1 EL0 CR1 CL0 DL0 AR0 BL1 AL1 CL1 HR1,RWL 8 2)::
(makeTM BR1 EL0 CR1 CR0 DL0 CR1 ER1 DL1 HR1 AR1,RWL 3 2)::
(makeTM BR1 EL0 CR1 CR0 DL1 AL0 HR1 BL1 ER1 BR0,RWL 3 2)::
(makeTM BR1 EL0 CR1 CR0 DL1 AL0 ER1 CL1 HR1 BR0,RWL 4 2)::
(makeTM BR1 EL0 CR1 CR0 DL1 AR1 HR1 AL0 ER1 BR1,RWL 4 2)::
(makeTM BR1 EL0 CR1 CR0 DR1 HR1 DL1 ER1 BL0 AL1,RWL 6 2)::
(makeTM BR1 EL0 CR1 CR0 DR1 HR1 ER1 DR0 AL1 DL0,RWL 2 3)::
(makeTM BR1 EL0 CR1 CL1 DL0 AR0 EL1 BL1 CR1 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR1 CL1 DL1 AR0 AL0 AR0 BL1 HR1,RWL 5 2)::
(makeTM BR1 EL0 CR1 DL0 DR0 HR1 AL1 DR1 AL0 CR0,RWL 4 2)::
(makeTM BR1 EL0 CR1 DR0 DL1 AL0 HR1 BL1 ER1 BR0,RWL 3 2)::
(makeTM BR1 EL0 CR1 DR0 DL1 AR0 BR0 AL0 CL0 HR1,RWL 2 2)::
(makeTM BR1 EL0 CR1 DR0 DL1 DL1 HR1 AL0 ER1 BR0,RWL 3 2)::
(makeTM BR1 EL0 CR1 DR0 DR1 HR1 ER1 AR0 AL1 EL1,RWL 1 3)::
(makeTM BR1 EL0 CR1 DL1 BL1 AR0 AL1 AR0 CL0 HR1,RWL 3 2)::
(makeTM BR1 EL0 CR1 DL1 BL1 DR0 CL1 AL0 HR1 CR0,RWL 6 2)::
(makeTM BR1 EL0 CR1 DL1 DL1 AL0 CR0 BL1 HR1 DR1,RWL 2 2)::
(makeTM BR1 EL0 CR1 DR1 CL1 BL1 HR1 AL0 ER1 BR0,RWL 3 2)::
(makeTM BR1 EL0 CR1 DR1 DL1 DL1 HR1 AL0 ER1 BR0,RWL 3 2)::
(makeTM BR1 EL0 CR1 ER1 DL1 HR1 EL1 BR0 AL1 DR0,RWL 3 2)::
(makeTM BR1 EL0 CR1 ER1 DR1 HR1 ER0 DR0 AL1 AL0,RWL 6 2)::
(makeTM BR1 ER0 BL0 CL1 DR1 CL1 HR1 AR1 CL0 ER1,RWL 2 2)::
(makeTM BR1 ER0 BL1 CL0 AL1 DL0 DR1 AR1 HR1 CR1,RWL 4 2)::
(makeTM BR1 ER0 BL1 CL0 DR1 CL0 AR0 HR1 BL0 CR0,RWL 8 2)::
(makeTM BR1 ER0 BL1 CL0 DR1 CL1 BR0 AR0 HR1 CL0,RWL 3 3)::
(makeTM BR1 ER0 BL1 CL0 DR1 CL1 BR0 AR0 HR1 DL1,RWL 3 3)::
(makeTM BR1 ER0 BL1 CL0 DR1 CL1 CL0 AR0 HR1 BR1,RWL 2 4)::
(makeTM BR1 ER0 BL1 CL0 DR1 CL1 EL1 AR0 HR1 BR1,RWL 2 4)::
(makeTM BR1 ER0 BL1 CL0 DR1 ER1 AR0 HR1 BL0 CR0,RWL 8 2)::
(makeTM BR1 ER0 BL1 CL1 AL1 DR1 HR1 AR0 EL1 CL0,RWL 14 2)::
(makeTM BR1 ER0 BL1 CR1 BR1 DL1 HR1 AR1 EL1 CL0,RWL 2 2)::
(makeTM BR1 ER0 CL0 HR1 DL1 CL1 AR1 AL0 CR1 DR1,RWL 2 4)::
(makeTM BR1 ER0 CL0 HR1 DL1 CL1 AR1 CL0 CR1 DR0,RWL 1 3)::
(makeTM BR1 ER0 CL0 HR1 DL1 CL1 AR1 DR1 BL1 AR1,RWL 4 2)::
(makeTM BR1 ER0 CL0 HR1 DL1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL0 HR1 DR1 CL1 HR1 AR1 CL0 ER1,RWL 2 2)::
(makeTM BR1 ER0 CL0 HR1 DR1 CL1 BL0 AR1 DR0 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL0 HR1 DR1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL0 AR0 AL1 DR1 EL1 HR1 CR1 BL1,RWL 2 2)::
(makeTM BR1 ER0 CL0 AR0 CR1 DR1 DL1 BL0 CR0 HR1,RWL 4 3)::
(makeTM BR1 ER0 CL0 AL1 CR1 DR0 AL1 ER0 HR1 BL1,RWL 2 2)::
(makeTM BR1 ER0 CL0 AR1 HR1 DL1 BR1 DL1 CL0 ER1,RWL 2 2)::
(makeTM BR1 ER0 CL0 AR1 DL0 CR1 BR1 DL1 HR1 CR1,RWL 2 2)::
(makeTM BR1 ER0 CL0 AR1 DR0 CL1 HR1 AL1 CL0 ER1,RWL 2 2)::
(makeTM BR1 ER0 CL0 AR1 DR1 BL1 BL0 HR1 EL1 CR0,RWL 1 4)::
(makeTM BR1 ER0 CL0 AR1 DR1 BL1 BR1 HR1 EL1 CR0,RWL 1 4)::
(makeTM BR1 ER0 CL0 AR1 DR1 CL1 HR1 BL0 CL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CL0 AR1 DR1 CL1 HR1 BR1 CL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CL0 AR1 DR1 CL1 HR1 BR1 DL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CL0 BL0 CR1 DR1 AL1 ER1 HR1 BL1,RWL 2 2)::
(makeTM BR1 ER0 CL0 BL0 DL0 CL1 DR1 AR1 HR1 AL1,RWL 3 2)::
(makeTM BR1 ER0 CL0 BL0 DL0 CL1 DR1 AR1 HR1 CL1,RWL 3 2)::
(makeTM BR1 ER0 CL0 BL0 DL0 CL1 DR1 AR1 HR1 CR1,RWL 3 2)::
(makeTM BR1 ER0 CL0 BR0 CL1 DL1 DR1 AL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER0 CL0 BR0 CL1 DL1 ER0 AL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER0 CL0 BR1 DL0 CL1 DR1 AR0 HR1 BR1,RWL 2 3)::
(makeTM BR1 ER0 CL0 BR1 DL0 CL1 DR1 AR0 HR1 CL1,RWL 2 3)::
(makeTM BR1 ER0 CL0 BR1 DL0 CL1 DR1 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR1 ER0 CL0 BR1 DL0 CL1 DR1 AR1 HR1 DR1,RWL 3 2)::
(makeTM BR1 ER0 CL0 BR1 DL1 CL1 AR1 AL1 HR1 AR1,RWL 4 2)::
(makeTM BR1 ER0 CL0 BR1 DL1 CL1 AR1 DL0 HR1 AR1,RWL 4 2)::
(makeTM BR1 ER0 CL0 BR1 DR1 CL1 HR1 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 ER0 CL0 BR1 DR1 CL1 HR1 AR1 BR0 EL1,RWL 2 2)::
(makeTM BR1 ER0 CL0 BR1 DR1 CL1 AR0 AR1 HR1 DL0,RWL 2 2)::
(makeTM BR1 ER0 CL0 BR1 DR1 CL1 BR0 AR1 HR1 DL1,RWL 2 2)::
(makeTM BR1 ER0 CL0 CL1 AR1 DL0 BL1 DR1 HR1 DR0,RWL 2 3)::
(makeTM BR1 ER0 CL0 CR1 HR1 DL1 DR1 AR1 BL1 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL0 DL0 DL0 CL1 DR1 AR1 HR1 DR1,RWL 3 2)::
(makeTM BR1 ER0 CL0 DL0 DR1 CL1 HR1 AR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 ER0 CL0 DL0 DR1 CL1 AR0 AR1 HR1 DL0,RWL 2 2)::
(makeTM BR1 ER0 CL0 DR0 AL1 CL1 AR1 CR0 HR1 CL0,RWL 4 2)::
(makeTM BR1 ER0 CL0 DR0 DL1 BL1 AR1 AL0 DR1 HR1,RWL 9 2)::
(makeTM BR1 ER0 CL0 DL1 DR1 BL0 AR1 CL1 CR1 HR1,RWL 3 2)::
(makeTM BR1 ER0 CL0 DR1 AL1 CL1 HR1 AR0 CL0 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL0 EL0 DL1 CL1 AR1 AL1 HR1 AR1,RWL 4 2)::
(makeTM BR1 ER0 CL0 EL0 DL1 CL1 AR1 DL0 HR1 AR1,RWL 4 2)::
(makeTM BR1 ER0 CL0 ER0 DL1 CL1 AR1 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 ER0 CL0 ER1 HR1 DL1 AR1 CL1 DL0 BR1,RWL 2 3)::
(makeTM BR1 ER0 CR0 HR1 CL1 DL0 ER0 AL1 DL1 AL0,RWL 2 2)::
(makeTM BR1 ER0 CR0 HR1 CL1 DL0 ER1 AL1 AL0 AL0,RWL 2 2)::
(makeTM BR1 ER0 CR0 HR1 CL1 DL0 ER1 AL1 AL0 BL1,RWL 2 2)::
(makeTM BR1 ER0 CR0 HR1 CL1 DL0 ER1 AL1 AL0 DL0,RWL 2 2)::
(makeTM BR1 ER0 CR0 HR1 CL1 DL0 ER1 AL1 AL1 AL0,RWL 2 2)::
(makeTM BR1 ER0 CR0 HR1 DL1 AR0 AL0 DL0 CL1 AR1,RWL 4 3)::
(makeTM BR1 ER0 CR0 HR1 DL1 CL1 AR1 CL0 CR1 DR0,RWL 1 3)::
(makeTM BR1 ER0 CR0 HR1 DL1 CR1 AL0 AL1 BL0 DL0,RWL 2 3)::
(makeTM BR1 ER0 CR0 HR1 DL1 CR1 AL0 AL1 DL1 DL0,RWL 2 3)::
(makeTM BR1 ER0 CR0 HR1 DL1 CR1 AL0 EL0 BL0 AL0,RWL 2 3)::
(makeTM BR1 ER0 CR0 AL0 DL1 HR1 AR1 BL0 CL1 DR1,RWL 5 2)::
(makeTM BR1 ER0 CR0 AR0 DL1 HR1 AL1 DL0 DR1 CL0,RWL 3 3)::
(makeTM BR1 ER0 CR0 AR0 DR1 HR1 EL1 BL0 AR1 DL0,RWL 2 2)::
(makeTM BR1 ER0 CR0 AR1 CL1 DR0 HR1 EL0 AL1 AL0,RWL 5 2)::
(makeTM BR1 ER0 CR0 AR1 CL1 DR0 AL1 DL0 HR1 AL0,RWL 5 2)::
(makeTM BR1 ER0 CR0 AR1 DL0 BR0 AL1 EL1 HR1 CL0,RWL 5 2)::
(makeTM BR1 ER0 CR0 AR1 DL1 AL1 CL0 HR1 BR0 AL0,RWL 1 4)::
(makeTM BR1 ER0 CR0 BR0 CL1 DL1 DR1 AL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER0 CR0 BR0 CL1 DL1 ER0 AL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER0 CR0 BR0 DL1 AL0 EL0 HR1 AL1 CL1,RWL 3 2)::
(makeTM BR1 ER0 CR0 CR1 DL1 AR0 AL0 DL0 CL0 HR1,RWL 12 2)::
(makeTM BR1 ER0 CR0 CR1 DL1 AL1 CL0 AR1 HR1 AL0,RWL 2 3)::
(makeTM BR1 ER0 CR0 CR1 DL1 DR0 ER1 AL1 HR1 BL0,RWL 2 2)::
(makeTM BR1 ER0 CR0 ER0 CL1 DL1 AL1 HR1 BR1 DL0,RWL 2 4)::
(makeTM BR1 ER0 CR0 EL1 DL1 BR0 BL0 HR1 AL0 CL1,RWL 4 2)::
(makeTM BR1 ER0 CR0 ER1 CL1 DL0 AL1 HR1 AR0 BL1,RWL 5 2)::
(makeTM BR1 ER0 CR0 ER1 CL1 DL1 AL1 EL0 HR1 CR0,RWL 3 2)::
(makeTM BR1 ER0 CR0 ER1 DR1 HR1 EL1 DL0 AR1 DL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 HR1 BR1 DL1 DR1 AR0 EL1 CL0,RWL 3 2)::
(makeTM BR1 ER0 CL1 HR1 DL0 CL1 ER1 DL0 AR1 DR0,RWL 3 3)::
(makeTM BR1 ER0 CL1 HR1 DL1 CL0 AR1 CL1 DR1 CR0,RWL 6 2)::
(makeTM BR1 ER0 CL1 HR1 DL1 CL0 EL1 ER0 ER1 AR1,RWL 2 3)::
(makeTM BR1 ER0 CL1 HR1 DL1 CL1 AR1 CL0 CR1 DR0,RWL 1 3)::
(makeTM BR1 ER0 CL1 AL0 HR1 DL0 DR1 AR1 EL1 BR0,RWL 3 2)::
(makeTM BR1 ER0 CL1 AL0 HR1 DL0 ER1 DL1 AR1 BL0,RWL 4 3)::
(makeTM BR1 ER0 CL1 AR0 HR1 DL0 EL1 HR1 AL1 EL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 AR0 HR1 DL1 AL1 HR1 EL1 DL0,RWL 14 2)::
(makeTM BR1 ER0 CL1 AR0 HR1 DL1 BR1 BL1 EL1 DL0,RWL 3 2)::
(makeTM BR1 ER0 CL1 AR0 AL0 DL0 AL1 HR1 CR0 BL0,RWL 3 3)::
(makeTM BR1 ER0 CL1 AR0 AL0 DL1 AL1 HR1 BR0 DL0,RWL 28 2)::
(makeTM BR1 ER0 CL1 AR0 AL1 DL0 BL0 HR1 AL1 BR0,RWL 4 2)::
(makeTM BR1 ER0 CL1 AR0 AL1 DL0 BR0 HR1 EL1 CL0,RWL 14 2)::
(makeTM BR1 ER0 CL1 AR0 AL1 DL0 BL1 HR1 BL0 CL0,RWL 3 2)::
(makeTM BR1 ER0 CL1 AR0 AL1 DR0 HR1 BL1 EL1 CL0,RWL 14 2)::
(makeTM BR1 ER0 CL1 AR0 AL1 DL1 AL1 HR1 EL1 CL0,RWL 14 2)::
(makeTM BR1 ER0 CL1 AR0 AL1 DL1 BL0 HR1 EL1 CL0,RWL 3 3)::
(makeTM BR1 ER0 CL1 AR0 AL1 DL1 CL0 HR1 DL0 BR1,RWL 2 3)::
(makeTM BR1 ER0 CL1 AR0 AR1 DL1 BL0 HR1 DL1 CL1,RWL 4 3)::
(makeTM BR1 ER0 CL1 AR0 AR1 DL1 CL0 BL0 DR0 HR1,RWL 57 2)::
(makeTM BR1 ER0 CL1 AR0 BR0 DL1 EL0 HR1 AL1 BL0,RWL 6 2)::
(makeTM BR1 ER0 CL1 AR0 BL1 DL1 AL1 HR1 CR0 DL0,RWL 5 3)::
(makeTM BR1 ER0 CL1 AR0 CL0 DL0 AL1 HR1 CL1 BR1,RWL 2 3)::
(makeTM BR1 ER0 CL1 AR0 CL0 DL0 AL1 HR1 CL1 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL1 AR0 CL0 DL1 AL1 HR1 CR0 DL0,RWL 5 2)::
(makeTM BR1 ER0 CL1 AR0 CL1 DL1 AL1 HR1 CR0 DL0,RWL 5 3)::
(makeTM BR1 ER0 CL1 AR0 DL0 BL0 ER1 AL1 AR1 HR1,RWL 4 2)::
(makeTM BR1 ER0 CL1 AR0 DL0 BL0 ER1 DL0 AR1 HR1,RWL 2 3)::
(makeTM BR1 ER0 CL1 AR0 DL0 BL1 AL1 HR1 EL1 DL0,RWL 3 3)::
(makeTM BR1 ER0 CL1 AR0 DR0 BL0 AR1 EL0 CL0 HR1,RWL 4 3)::
(makeTM BR1 ER0 CL1 AR0 DL1 BL1 AL1 HR1 EL1 DL0,RWL 3 3)::
(makeTM BR1 ER0 CL1 AR0 DL1 BL1 BR1 DL0 HR1 CR0,RWL 7 2)::
(makeTM BR1 ER0 CL1 AR0 DL1 CL1 AL1 CR0 HR1 DL0,RWL 6 2)::
(makeTM BR1 ER0 CL1 AR0 DL1 CL1 AL1 DL1 HR1 DL0,RWL 6 2)::
(makeTM BR1 ER0 CL1 AR0 DL1 CL1 BR1 DR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 ER0 CL1 AR0 DL1 CL1 BR1 DR1 HR1 DL1,RWL 2 2)::
(makeTM BR1 ER0 CL1 AR0 DL1 CR1 AL1 DL1 HR1 DL0,RWL 3 2)::
(makeTM BR1 ER0 CL1 AR0 DR1 BL0 ER1 DL0 AR1 HR1,RWL 4 2)::
(makeTM BR1 ER0 CL1 AR0 DR1 CL1 AL1 DL1 HR1 DL0,RWL 6 2)::
(makeTM BR1 ER0 CL1 AR0 ER0 DL1 AL1 HR1 BL1 DL0,RWL 14 2)::
(makeTM BR1 ER0 CL1 AR0 EL1 DL1 AL1 HR1 BL1 DL0,RWL 14 2)::
(makeTM BR1 ER0 CL1 AL1 DR1 BL0 AR0 AR1 HR1 DL0,RWL 9 2)::
(makeTM BR1 ER0 CL1 AL1 EL1 DR1 BR1 BR0 HR1 DL0,RWL 2 2)::
(makeTM BR1 ER0 CL1 AR1 HR1 DL0 AL1 ER1 AL0 CR0,RWL 4 2)::
(makeTM BR1 ER0 CL1 AR1 HR1 DL0 AR1 BR1 CL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CL1 AR1 HR1 DL0 EL0 DL1 AR1 BL0,RWL 24 2)::
(makeTM BR1 ER0 CL1 AR1 HR1 DR1 BR1 BL1 EL1 DL0,RWL 2 2)::
(makeTM BR1 ER0 CL1 AR1 AR0 DL0 CL1 AL0 CL0 HR1,RWL 35 2)::
(makeTM BR1 ER0 CL1 AR1 CL1 DL0 AL1 AL1 HR1 CR0,RWL 12 2)::
(makeTM BR1 ER0 CL1 AR1 DL0 CR1 AL1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 ER0 CL1 AR1 DL1 CL1 BR1 DR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER0 CL1 AR1 DR1 CL1 HR1 BL0 CL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CL1 AR1 DR1 CL1 HR1 BR1 CL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CL1 BR0 AR1 DL1 AL1 HR1 BR1 DL0,RWL 24 2)::
(makeTM BR1 ER0 CL1 BR0 DL0 AL1 AR1 DL1 HR1 BL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR0 DL1 DR0 AR1 BL0 HR1 AR1,RWL 4 2)::
(makeTM BR1 ER0 CL1 BL1 HR1 DL1 EL1 DL0 AR1 DR0,RWL 10 3)::
(makeTM BR1 ER0 CL1 BL1 DR1 BL0 HR1 AR1 DR0 AR1,RWL 35 2)::
(makeTM BR1 ER0 CL1 BL1 DR1 BL0 HR1 AR1 DR0 EL1,RWL 35 2)::
(makeTM BR1 ER0 CL1 BL1 DR1 CR1 BL1 AR0 HR1 CL1,RWL 2 2)::
(makeTM BR1 ER0 CL1 BL1 DR1 CR1 BL1 AR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER0 CL1 BL1 ER1 DR1 BL0 DR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER0 CL1 BR1 HR1 DL0 AR1 DR0 EL1 BL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR1 HR1 DL0 AR1 DL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR1 HR1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR1 AL0 DL0 AR1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR1 AR0 DL0 AR1 DL1 HR1 CL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR1 AR1 DL0 AR1 BL1 HR1 BR0,RWL 3 4)::
(makeTM BR1 ER0 CL1 BR1 AR1 DL0 BL0 AL0 CR0 HR1,RWL 3 3)::
(makeTM BR1 ER0 CL1 BR1 AR1 DL0 DR1 BL1 HR1 BR0,RWL 3 4)::
(makeTM BR1 ER0 CL1 BR1 BR0 DL0 AR1 DL1 HR1 CL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR1 BR0 DL0 AR1 DL1 HR1 CL1,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR1 BL1 DL0 AR1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 ER0 CL1 BR1 ER1 DL1 AR0 BL0 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER0 CL1 CR0 HR1 DL1 AR1 DL0 DR1 AR1,RWL 34 2)::
(makeTM BR1 ER0 CL1 CR0 AL0 DL0 AR1 DL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 ER0 CL1 CR0 AL0 DL0 AR1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 ER0 CL1 CR0 AR0 DL0 BL1 HR1 AL1 CR1,RWL 3 3)::
(makeTM BR1 ER0 CL1 CR0 AR0 DL0 BL1 HR1 BL1 CR1,RWL 3 3)::
(makeTM BR1 ER0 CL1 CR0 AR0 DL0 BL1 HR1 CR1 CR1,RWL 3 3)::
(makeTM BR1 ER0 CL1 CR0 AR0 DL0 BL1 HR1 EL0 CR1,RWL 3 3)::
(makeTM BR1 ER0 CL1 CR0 AR1 DL0 AR1 BL0 BR1 HR1,RWL 3 4)::
(makeTM BR1 ER0 CL1 CR0 AR1 DL0 ER1 BL0 BR1 HR1,RWL 3 4)::
(makeTM BR1 ER0 CL1 CR0 AR1 DL1 CL1 CL0 HR1 DR0,RWL 5 2)::
(makeTM BR1 ER0 CL1 CR0 AR1 DR1 AL1 DL1 HR1 DL0,RWL 7 2)::
(makeTM BR1 ER0 CL1 CR0 DR1 DL0 AR1 DL1 HR1 BR1,RWL 2 3)::
(makeTM BR1 ER0 CL1 CR1 AL0 DL0 AR1 BL0 AR1 HR1,RWL 3 2)::
(makeTM BR1 ER0 CL1 DL0 AL1 BL0 DR1 AR1 HR1 AL1,RWL 1 4)::
(makeTM BR1 ER0 CL1 DL0 AL1 BL0 DR1 AR1 HR1 CL1,RWL 1 4)::
(makeTM BR1 ER0 CL1 DL0 BR0 DL1 AR1 CL1 HR1 AR1,RWL 2 4)::
(makeTM BR1 ER0 CL1 DR0 HR1 AL1 EL1 DR1 BL0 AL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 DR0 AL1 CL1 AR1 CR1 HR1 CL0,RWL 7 2)::
(makeTM BR1 ER0 CL1 DR0 AL1 DL1 BL1 AR0 HR1 CR0,RWL 2 3)::
(makeTM BR1 ER0 CL1 DR0 BR1 AL1 EL1 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 DR0 DL1 AL1 HR1 AR1 AL0 BL1,RWL 2 3)::
(makeTM BR1 ER0 CL1 DR0 DR1 BL0 BL1 AR1 HR1 AL1,RWL 6 3)::
(makeTM BR1 ER0 CL1 DL1 HR1 DL0 AR1 BL1 AL0 ER1,RWL 4 3)::
(makeTM BR1 ER0 CL1 DL1 HR1 DL0 AR1 BL1 CL1 ER1,RWL 4 3)::
(makeTM BR1 ER0 CL1 DL1 HR1 DL0 AR1 BL1 DR0 ER1,RWL 4 3)::
(makeTM BR1 ER0 CL1 DL1 DR1 BL1 AR1 DL0 HR1 CR1,RWL 15 2)::
(makeTM BR1 ER0 CL1 DR1 HR1 DL0 AR1 AL0 DL0 BR0,RWL 4 2)::
(makeTM BR1 ER0 CL1 DR1 AR0 AL1 ER0 EL1 HR1 CL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 DR1 AR0 DL0 AL1 EL1 HR1 CL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 DR1 BR1 CL1 HR1 AR1 CL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CL1 DR1 CL1 AL1 HR1 BR1 BL0 ER0,RWL 2 2)::
(makeTM BR1 ER0 CL1 DR1 CL1 AL1 HR1 BR1 BR0 ER0,RWL 2 2)::
(makeTM BR1 ER0 CL1 DR1 CL1 AL1 HR1 BR1 CL0 ER0,RWL 2 2)::
(makeTM BR1 ER0 CL1 DR1 CL1 AL1 HR1 BR1 CR0 ER0,RWL 2 2)::
(makeTM BR1 ER0 CL1 DR1 DR0 BL0 AR0 CL0 AL1 HR1,RWL 5 2)::
(makeTM BR1 ER0 CL1 DR1 DL1 AL1 HR1 AL0 AR1 BL1,RWL 2 3)::
(makeTM BR1 ER0 CL1 DR1 ER1 AL1 HR1 BR1 AL0 CL0,RWL 2 2)::
(makeTM BR1 ER0 CL1 EL0 ER1 DL0 BL0 HR1 AR0 ER1,RWL 17 2)::
(makeTM BR1 ER0 CL1 EL1 HR1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL1 EL1 AL0 DL0 AR1 DL1 HR1 CR0,RWL 2 3)::
(makeTM BR1 ER0 CL1 ER1 HR1 DL0 AR1 DL1 CL1 BR1,RWL 2 3)::
(makeTM BR1 ER0 CL1 ER1 HR1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 ER0 CL1 ER1 HR1 DL1 AR1 CL0 BR1 DL0,RWL 2 3)::
(makeTM BR1 ER0 CL1 ER1 DR1 CL0 AR0 HR1 EL1 CR1,RWL 15 2)::
(makeTM BR1 ER0 CR1 HR1 DL0 AR0 AL0 DL1 DL0 ER1,RWL 2 2)::
(makeTM BR1 ER0 CR1 HR1 DL0 AR1 BR0 EL0 CL1 ER1,RWL 4 2)::
(makeTM BR1 ER0 CR1 HR1 DL0 AR1 BR1 EL0 CL1 ER1,RWL 5 2)::
(makeTM BR1 ER0 CR1 HR1 DR0 AL0 DL1 ER1 BL0 CL0,RWL 2 2)::
(makeTM BR1 ER0 CR1 HR1 DL1 AL0 CR0 AL1 DL0 CL1,RWL 2 2)::
(makeTM BR1 ER0 CR1 HR1 DL1 CL0 AR1 CL1 DR1 CR0,RWL 6 2)::
(makeTM BR1 ER0 CR1 HR1 DL1 CL0 AR1 CL1 ER1 DR0,RWL 4 2)::
(makeTM BR1 ER0 CR1 HR1 DL1 CL1 AR1 CL0 CR1 DR0,RWL 1 3)::
(makeTM BR1 ER0 CR1 HR1 DL1 DL0 AR1 DL1 CL1 ER1,RWL 2 3)::
(makeTM BR1 ER0 CR1 HR1 DR1 CL1 CL0 AR1 CR0 DL0,RWL 11 3)::
(makeTM BR1 ER0 CR1 AL0 DL1 AR0 BL1 DL0 DR1 HR1,RWL 6 2)::
(makeTM BR1 ER0 CR1 AR0 DL1 HR1 EL0 DL1 AR1 EL0,RWL 3 3)::
(makeTM BR1 ER0 CR1 AR0 DL1 CL1 HR1 EL1 AL1 EL0,RWL 10 3)::
(makeTM BR1 ER0 CR1 AR0 DL1 CR1 AL1 DL1 HR1 DL0,RWL 3 2)::
(makeTM BR1 ER0 CR1 AL1 DL0 CL1 AR1 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 ER0 CR1 AL1 DL1 DR0 HR1 AL0 AL1 BL0,RWL 2 2)::
(makeTM BR1 ER0 CR1 AL1 DR1 CR0 BL1 AR1 HR1 DL0,RWL 6 2)::
(makeTM BR1 ER0 CR1 AR1 DL0 CR1 AL1 DL1 HR1 CR0,RWL 2 2)::
(makeTM BR1 ER0 CR1 AR1 DL1 HR1 AL1 AL0 DL0 ER1,RWL 1 3)::
(makeTM BR1 ER0 CR1 BL0 DL1 DR0 AR1 BL1 HR1 AR1,RWL 4 3)::
(makeTM BR1 ER0 CR1 BL0 DL1 DR0 AR1 BL1 HR1 CL0,RWL 15 2)::
(makeTM BR1 ER0 CR1 BL0 DL1 DR0 AR1 BL1 HR1 CL1,RWL 15 2)::
(makeTM BR1 ER0 CR1 BR0 DL1 AR0 AL0 CL0 BL0 HR1,RWL 4 2)::
(makeTM BR1 ER0 CR1 BR0 DL1 AR0 AL0 CL0 DR0 HR1,RWL 20 2)::
(makeTM BR1 ER0 CR1 BR0 DL1 AR0 AL1 CL1 HR1 CL0,RWL 4 3)::
(makeTM BR1 ER0 CR1 BR0 DL1 EL0 AL1 BL1 HR1 CL1,RWL 5 2)::
(makeTM BR1 ER0 CR1 BL1 BL0 DR1 HR1 AR1 BL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CR1 BL1 BL1 DR1 HR1 AR1 BL0 ER1,RWL 3 2)::
(makeTM BR1 ER0 CR1 BL1 DL1 AR1 HR1 BL1 DL0 ER1,RWL 2 2)::
(makeTM BR1 ER0 CR1 BL1 DL1 AR1 BL0 DR1 HR1 DR1,RWL 2 2)::
(makeTM BR1 ER0 CR1 BL1 DL1 DL0 AR1 DL1 HR1 CR0,RWL 1 4)::
(makeTM BR1 ER0 CR1 BL1 DR1 AR1 BL0 DR1 HR1 DR1,RWL 2 2)::
(makeTM BR1 ER0 CR1 BR1 CL1 DL1 HR1 AL1 CL0 ER0,RWL 3 2)::
(makeTM BR1 ER0 CR1 BR1 DL1 CL1 AR0 EL1 HR1 DL0,RWL 2 2)::
(makeTM BR1 ER0 CR1 CL1 DL0 AR1 BL1 CR0 HR1 DR1,RWL 4 2)::
(makeTM BR1 ER0 CR1 DR0 DL1 HR1 AL0 AR0 EL1 DL0,RWL 8 2)::
(makeTM BR1 ER0 CR1 DR0 DL1 BL1 AR1 CL0 BR1 HR1,RWL 4 3)::
(makeTM BR1 ER0 CR1 DL1 BL1 HR1 AR1 BL0 ER1 DR0,RWL 2 2)::
(makeTM BR1 ER0 CR1 DL1 BL1 DR0 HR1 AL0 ER1 DL0,RWL 2 3)::
(makeTM BR1 ER0 CR1 DL1 DL1 AR1 HR1 AL0 BL0 ER1,RWL 3 3)::
(makeTM BR1 ER0 CR1 DR1 DL1 BR0 AR1 CL0 AL1 HR1,RWL 2 3)::
(makeTM BR1 ER0 CR1 DR1 DL1 BR1 AL1 DL0 HR1 AR1,RWL 5 2)::
(makeTM BR1 ER0 CR1 DR1 DL1 EL0 AL1 DL0 HR1 AR1,RWL 5 2)::
(makeTM BR1 ER0 CR1 EL1 DR1 HR1 EL1 DR0 AL1 BL0,RWL 4 4)::
(makeTM BR1 ER0 CR1 ER1 DL1 HR1 AL1 EL1 AR1 DL0,RWL 10 3)::
(makeTM BR1 EL1 BL0 CR0 DL1 CR1 CR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 BL0 CL1 DR1 CR0 AL1 DR0 BL1 HR1,RWL 8 4)::
(makeTM BR1 EL1 BL0 CR1 BL1 DR0 DL1 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR1 EL1 BL0 CR1 BL1 DR0 DL1 AL0 HR1 DR0,RWL 2 2)::
(makeTM BR1 EL1 BL1 CL0 CR1 DR0 AL0 DR1 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL1 BL1 CL0 CR1 DR0 AL0 DR1 HR1 CL0,RWL 2 3)::
(makeTM BR1 EL1 BL1 CL0 DR1 CL1 AR1 ER0 HR1 BR0,RWL 1 3)::
(makeTM BR1 EL1 BL1 CL1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 BL1 CL1 DR1 CR1 AL1 DL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 EL1 BL1 CR1 HR1 DR0 DL1 AL0 BR0 EL1,RWL 2 3)::
(makeTM BR1 EL1 BL1 CR1 AL1 DR1 BL0 DR0 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL1 BL1 CR1 DR0 BL0 DL1 AL0 HR1 CR1,RWL 2 2)::
(makeTM BR1 EL1 BL1 CR1 DR0 BL0 DL1 AL0 HR1 DR0,RWL 2 2)::
(makeTM BR1 EL1 BL1 CR1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL0 HR1 DR0 CL1 AL1 DR1 CL1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL0 HR1 DR0 CL1 AL1 DR1 CR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL0 HR1 DR0 CL1 AL1 DR1 DR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL0 HR1 EL1 DR0 CR1 AR1 DL1 BL0,RWL 4 2)::
(makeTM BR1 EL1 CL0 AR0 HR1 DL1 CR1 AL1 DL0 DL1,RWL 3 2)::
(makeTM BR1 EL1 CL0 AR0 AR1 DL1 AL1 BL1 BL0 HR1,RWL 3 3)::
(makeTM BR1 EL1 CL0 AR0 DR0 DL1 AL1 CL0 DL0 HR1,RWL 14 2)::
(makeTM BR1 EL1 CL0 AR0 DR1 CR0 AL1 BL1 DL0 HR1,RWL 5 2)::
(makeTM BR1 EL1 CL0 AR1 HR1 DL1 BR1 CL1 BR0 AL0,RWL 2 2)::
(makeTM BR1 EL1 CL0 BL0 CR1 DR1 EL1 BL0 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL1 CL0 BL0 CR1 DR1 EL1 BL1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL1 CL0 BR0 AR1 DL1 BL1 CL1 HR1 AL0,RWL 2 4)::
(makeTM BR1 EL1 CL0 BR0 CL1 DR1 EL1 BR1 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL1 CL0 BR1 DR1 CL1 AL0 BR0 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CL0 CR0 DR0 AL1 DL1 AL0 HR1 BL0,RWL 3 2)::
(makeTM BR1 EL1 CL0 CL1 AL0 DR0 ER1 HR1 BL1 ER0,RWL 12 2)::
(makeTM BR1 EL1 CL0 DR0 HR1 AL1 AR1 AR0 ER1 CL1,RWL 3 2)::
(makeTM BR1 EL1 CL0 DR0 HR1 AL1 ER1 AL0 AR1 BL1,RWL 3 2)::
(makeTM BR1 EL1 CL0 DR0 AL1 CR0 DL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL1 CL0 DR0 AL1 CR0 DL1 AL0 HR1 DR0,RWL 2 2)::
(makeTM BR1 EL1 CL0 DR1 AL1 BL1 AL0 CR0 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL1 CL0 DR1 AL1 BL1 BR0 BL0 DL1 HR1,RWL 4 2)::
(makeTM BR1 EL1 CL0 DR1 AL1 BL1 CR1 CR0 HR1 AL1,RWL 2 2)::
(makeTM BR1 EL1 CL0 DR1 AL1 CL1 HR1 BR0 AR1 ER1,RWL 2 2)::
(makeTM BR1 EL1 CL0 ER0 DL1 CL1 AR1 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL1 CR0 HR1 DR0 CR0 DL1 AR1 AL0 EL0,RWL 2 3)::
(makeTM BR1 EL1 CR0 HR1 DR1 AL0 DL1 CL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 EL1 CR0 HR1 DR1 CR1 AL1 DL0 AL0 ER0,RWL 9 2)::
(makeTM BR1 EL1 CR0 HR1 DR1 DR0 AL0 ER0 DL1 BL0,RWL 4 3)::
(makeTM BR1 EL1 CR0 AL0 CL1 DL1 AR1 BR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 EL1 CR0 AL0 DR0 HR1 DL1 AL1 BR0 DL1,RWL 3 2)::
(makeTM BR1 EL1 CR0 AL0 DR1 AL0 DL1 CL0 HR1 BR0,RWL 2 3)::
(makeTM BR1 EL1 CR0 AR0 CL1 DL0 AR0 AL0 DR0 HR1,RWL 5 3)::
(makeTM BR1 EL1 CR0 AR0 CL1 DL0 AL1 HR1 ER0 CR0,RWL 6 3)::
(makeTM BR1 EL1 CR0 AR1 CL1 DL1 BR1 AL0 HR1 DR0,RWL 6 2)::
(makeTM BR1 EL1 CR0 AR1 CL1 DR1 HR1 AL0 BR1 DR0,RWL 4 2)::
(makeTM BR1 EL1 CR0 AR1 DL1 AR1 CL1 HR1 ER0 AL0,RWL 2 2)::
(makeTM BR1 EL1 CR0 AR1 DR1 HR1 AL1 AR0 DL0 EL0,RWL 4 2)::
(makeTM BR1 EL1 CR0 BL0 DL1 HR1 ER1 BR0 AL1 DR0,RWL 2 2)::
(makeTM BR1 EL1 CR0 BL0 DL1 AR0 AL0 BR1 CL0 HR1,RWL 6 2)::
(makeTM BR1 EL1 CR0 BL0 DR1 HR1 ER1 DL0 AL1 BR0,RWL 3 2)::
(makeTM BR1 EL1 CR0 BL0 DR1 AR1 BL1 DL1 HR1 AL0,RWL 15 2)::
(makeTM BR1 EL1 CR0 BR0 CL1 DL0 AL1 DR1 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CR0 BR0 CL1 DR1 AL0 AR0 DL1 HR1,RWL 7 2)::
(makeTM BR1 EL1 CR0 BL1 DL1 CR1 BR0 AL1 HR1 BL0,RWL 3 2)::
(makeTM BR1 EL1 CR0 BL1 DL1 CR1 CR0 AL1 HR1 BL0,RWL 3 2)::
(makeTM BR1 EL1 CR0 BL1 DR1 AL0 DL1 CL0 HR1 BR0,RWL 2 3)::
(makeTM BR1 EL1 CR0 BR1 CL1 DL0 AL1 AL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL1 CR0 BR1 DL0 CR0 DL1 AL1 HR1 CR1,RWL 2 2)::
(makeTM BR1 EL1 CR0 BR1 DR0 CR0 DL1 AL1 HR1 CL1,RWL 2 2)::
(makeTM BR1 EL1 CR0 BR1 DR0 CR0 DL1 AL1 HR1 CR1,RWL 2 2)::
(makeTM BR1 EL1 CR0 BR1 DL1 CR0 AL1 HR1 DL1 AL0,RWL 4 3)::
(makeTM BR1 EL1 CR0 BR1 DR1 AR1 ER1 HR1 CL1 AL0,RWL 5 2)::
(makeTM BR1 EL1 CR0 CL0 DR1 AL0 BL1 CL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 EL1 CR0 CL0 DR1 AR1 ER1 HR1 CL1 AL0,RWL 5 2)::
(makeTM BR1 EL1 CR0 CR0 DR1 AL0 DL1 CL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL1 CR0 CR1 DL0 BR0 DL1 AL0 BL0 HR1,RWL 2 3)::
(makeTM BR1 EL1 CR0 CR1 DL0 BR0 DL1 AL0 DL0 HR1,RWL 2 3)::
(makeTM BR1 EL1 CR0 DL0 CL1 AL1 HR1 AR1 BR0 ER0,RWL 3 2)::
(makeTM BR1 EL1 CR0 DR0 AL1 HR1 DL1 AR1 CR0 EL0,RWL 3 2)::
(makeTM BR1 EL1 CR0 DR0 AL1 AL0 CL1 DR1 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CR0 DR0 AL1 AL0 DL1 CL0 HR1 CR0,RWL 2 3)::
(makeTM BR1 EL1 CR0 DR0 DL1 HR1 EL0 AL1 CR1 BL0,RWL 3 2)::
(makeTM BR1 EL1 CR0 DR0 DL1 AL0 CL1 DR1 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CR0 EL0 DR1 HR1 AL0 ER0 AR1 DL0,RWL 6 2)::
(makeTM BR1 EL1 CR0 EL0 DR1 AL0 DL1 CL0 HR1 BR1,RWL 2 3)::
(makeTM BR1 EL1 CR0 ER0 DR0 HR1 AL1 BL0 DL1 DR1,RWL 1 3)::
(makeTM BR1 EL1 CR0 ER1 CL1 DR1 HR1 AL0 BR1 DR0,RWL 5 2)::
(makeTM BR1 EL1 CR0 ER1 DL0 DR0 AL1 HR1 CL0 AL0,RWL 6 2)::
(makeTM BR1 EL1 CR0 ER1 DL1 AR0 CL1 HR1 AL1 AL0,RWL 12 2)::
(makeTM BR1 EL1 CR0 ER1 DL1 BR0 CL1 HR1 AL0 AL1,RWL 2 2)::
(makeTM BR1 EL1 CL1 AL0 AL1 DR1 HR1 BR0 BR0 DL0,RWL 3 2)::
(makeTM BR1 EL1 CL1 AL0 BL1 DR1 HR1 BR0 CR0 EL1,RWL 2 3)::
(makeTM BR1 EL1 CL1 AL0 BL1 DR1 HR1 CR1 DR0 BR0,RWL 2 3)::
(makeTM BR1 EL1 CL1 AL0 CR1 DR1 HR1 ER1 BL1 BR0,RWL 2 3)::
(makeTM BR1 EL1 CL1 AL0 DL1 CR1 HR1 BL1 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL1 CL1 AR0 HR1 DL0 EL1 AL0 BR1 BL1,RWL 10 2)::
(makeTM BR1 EL1 CL1 AR0 HR1 DL1 BR1 AL0 AR1 CL0,RWL 8 2)::
(makeTM BR1 EL1 CL1 AR0 HR1 DL1 BR1 AL0 CL0 AR0,RWL 8 2)::
(makeTM BR1 EL1 CL1 AR0 HR1 DL1 BR1 AL0 CL0 CL0,RWL 8 2)::
(makeTM BR1 EL1 CL1 AR0 HR1 DL1 ER1 AL0 CL0 AR0,RWL 8 2)::
(makeTM BR1 EL1 CL1 AR0 DL0 BL1 AL1 HR1 EL0 CR0,RWL 7 2)::
(makeTM BR1 EL1 CL1 AR0 DL1 CL0 AL1 AL0 BL0 HR1,RWL 4 2)::
(makeTM BR1 EL1 CL1 AL1 DR1 BL0 AR1 DR0 HR1 CR0,RWL 4 2)::
(makeTM BR1 EL1 CL1 AR1 BL1 DR1 HR1 BR0 DL0 AL0,RWL 2 3)::
(makeTM BR1 EL1 CL1 AR1 DR1 DL1 BR0 AL0 HR1 CL0,RWL 4 3)::
(makeTM BR1 EL1 CL1 AR1 EL1 DR1 HR1 BR0 DL0 AL0,RWL 2 3)::
(makeTM BR1 EL1 CL1 BR0 AL0 DL0 AR0 BL1 AL1 HR1,RWL 5 2)::
(makeTM BR1 EL1 CL1 BR0 DL0 CL0 AL1 AR1 HR1 CL1,RWL 6 3)::
(makeTM BR1 EL1 CL1 BR0 DL0 DL0 AL1 AR0 AL0 HR1,RWL 4 2)::
(makeTM BR1 EL1 CL1 BR0 DR0 CL0 AL1 AR1 HR1 AL0,RWL 2 4)::
(makeTM BR1 EL1 CL1 BR1 HR1 DL1 AR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 EL1 CL1 CR0 AL0 DR1 EL0 CR1 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CL1 CR0 AR1 DL1 BL0 AL0 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL1 CR0 AR1 DL1 BR1 CL1 HR1 AL0,RWL 4 3)::
(makeTM BR1 EL1 CL1 CR0 DL1 CR1 CL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CL1 CR0 DL1 CR1 CR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CL1 CR0 DR1 CL1 HR1 AR1 BR1 AL0,RWL 20 2)::
(makeTM BR1 EL1 CL1 CL1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL1 CR1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL1 DR0 HR1 AL1 AL0 ER1 AL1 BL0,RWL 3 2)::
(makeTM BR1 EL1 CL1 DR0 HR1 AL1 AR0 ER1 AL0 BL0,RWL 3 2)::
(makeTM BR1 EL1 CL1 DR0 AL1 CL0 AR0 HR1 AR1 ER1,RWL 6 2)::
(makeTM BR1 EL1 CL1 DR0 AL1 CR0 CL1 AL0 BL0 HR1,RWL 4 2)::
(makeTM BR1 EL1 CL1 DR0 AL1 CL1 AL0 CR0 HR1 CL0,RWL 6 2)::
(makeTM BR1 EL1 CL1 DR0 AL1 CL1 BL1 CR0 HR1 CL0,RWL 6 2)::
(makeTM BR1 EL1 CL1 DR0 AL1 CL1 DL1 AL1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL1 DR0 DL0 AL1 HR1 AR1 CL1 AR0,RWL 3 2)::
(makeTM BR1 EL1 CL1 DR0 DL0 CL1 AR1 AL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 EL1 CL1 DR0 DR1 BL0 AR1 AR0 HR1 CL0,RWL 3 3)::
(makeTM BR1 EL1 CL1 DL1 BL1 CR1 HR1 AL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL1 CL1 DL1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL1 DL1 DR1 BL0 AL1 CR0 DL1 HR1,RWL 2 3)::
(makeTM BR1 EL1 CL1 DR1 AL0 AL1 HR1 BR0 AL1 DR0,RWL 2 3)::
(makeTM BR1 EL1 CL1 DR1 AL1 BL1 CL0 AR0 DL0 HR1,RWL 2 2)::
(makeTM BR1 EL1 CL1 DR1 AR1 BR0 CL0 ER0 HR1 CL0,RWL 3 2)::
(makeTM BR1 EL1 CL1 DR1 CR1 AL1 HR1 BR1 CR0 EL0,RWL 2 2)::
(makeTM BR1 EL1 CL1 DR1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CL1 ER0 DL1 CL0 AL1 HR1 BR0 DL0,RWL 4 2)::
(makeTM BR1 EL1 CL1 ER0 EL0 DL0 AL1 HR1 BR0 AL0,RWL 2 3)::
(makeTM BR1 EL1 CR1 HR1 DL1 ER0 AR0 AL0 AL0 DR0,RWL 15 2)::
(makeTM BR1 EL1 CR1 HR1 DL1 ER0 BL0 AL0 CL0 DR0,RWL 17 2)::
(makeTM BR1 EL1 CR1 HR1 DR1 AL0 AL0 BR0 DR0 EL0,RWL 3 3)::
(makeTM BR1 EL1 CR1 HR1 DR1 CL0 AL1 ER0 AR1 CL1,RWL 35 2)::
(makeTM BR1 EL1 CR1 AL0 DL0 BR0 BL1 DL1 HR1 CL1,RWL 2 2)::
(makeTM BR1 EL1 CR1 AL0 DR0 HR1 EL1 ER0 BL0 EL0,RWL 6 2)::
(makeTM BR1 EL1 CR1 AL0 DL1 DR0 HR1 AR1 DL1 BL1,RWL 7 2)::
(makeTM BR1 EL1 CR1 AR0 DL0 CL1 AL1 BL1 BL0 HR1,RWL 4 3)::
(makeTM BR1 EL1 CR1 AR0 DL1 AR1 HR1 CL1 ER0 AL0,RWL 6 2)::
(makeTM BR1 EL1 CR1 AR0 DR1 AL1 CL1 HR1 AR1 CL0,RWL 12 2)::
(makeTM BR1 EL1 CR1 AR0 DR1 AL1 CL1 HR1 CL0 BL1,RWL 17 2)::
(makeTM BR1 EL1 CR1 AR0 DR1 AL1 ER1 HR1 CL0 BL1,RWL 13 2)::
(makeTM BR1 EL1 CR1 AL1 DR0 HR1 AL1 AR0 DR1 EL0,RWL 8 2)::
(makeTM BR1 EL1 CR1 AL1 DR1 HR1 BL0 DR0 DL1 DL0,RWL 4 2)::
(makeTM BR1 EL1 CR1 AR1 DR0 BR0 EL1 HR1 AL0 CL0,RWL 2 2)::
(makeTM BR1 EL1 CR1 BL0 DL1 CR0 AL0 AR1 HR1 BL1,RWL 7 4)::
(makeTM BR1 EL1 CR1 BL0 DL1 CR0 AL0 BL1 HR1 BR0,RWL 7 4)::
(makeTM BR1 EL1 CR1 BL0 DL1 CR0 AL0 BL1 HR1 BL1,RWL 7 4)::
(makeTM BR1 EL1 CR1 BL0 DL1 DR0 AR1 BL1 HR1 AL0,RWL 15 2)::
(makeTM BR1 EL1 CR1 BL0 DR1 DR0 AL1 AR1 HR1 BL1,RWL 15 2)::
(makeTM BR1 EL1 CR1 BR0 DL0 AR0 HR1 CL1 AR1 EL0,RWL 4 2)::
(makeTM BR1 EL1 CR1 BR0 DL0 AR0 AL1 CL1 DL1 HR1,RWL 4 2)::
(makeTM BR1 EL1 CR1 BR0 DL0 AR1 AL1 CL1 HR1 CL1,RWL 7 2)::
(makeTM BR1 EL1 CR1 BR0 DL0 DR0 AL0 DL1 HR1 BL0,RWL 7 2)::
(makeTM BR1 EL1 CR1 BL1 BL1 DR0 AL0 DR1 HR1 BL0,RWL 6 3)::
(makeTM BR1 EL1 CR1 BL1 DL1 DR0 AL0 DR1 HR1 BL0,RWL 6 3)::
(makeTM BR1 EL1 CR1 BL1 DR1 DR0 AL0 DR1 HR1 BL0,RWL 6 3)::
(makeTM BR1 EL1 CR1 BR1 DL0 CL1 AR1 EL1 HR1 AL0,RWL 2 2)::
(makeTM BR1 EL1 CR1 BR1 DL1 CL1 BR1 ER1 HR1 AL0,RWL 2 2)::
(makeTM BR1 EL1 CR1 BR1 DR1 HR1 AL1 DL0 DR1 AL1,RWL 3 4)::
(makeTM BR1 EL1 CR1 CL0 DL0 AR0 BL1 AL0 DL0 HR1,RWL 3 3)::
(makeTM BR1 EL1 CR1 CR0 DL1 CR1 CL1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CR1 CR0 DL1 CR1 CR1 EL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CR1 CR0 DL1 ER1 AL1 BL0 HR1 DR0,RWL 3 3)::
(makeTM BR1 EL1 CR1 CR0 DR1 BL0 EL1 CL0 HR1 AL1,RWL 2 3)::
(makeTM BR1 EL1 CR1 CL1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CR1 DL0 DL1 CR0 AL0 CL0 HR1 BL1,RWL 4 3)::
(makeTM BR1 EL1 CR1 DR0 BL0 AL1 DL1 AL0 HR1 BR1,RWL 2 2)::
(makeTM BR1 EL1 CR1 DR0 BL0 AL1 DL1 AL0 HR1 CR0,RWL 2 2)::
(makeTM BR1 EL1 CR1 DR0 DL1 BR1 HR1 AL0 CR0 DR0,RWL 3 2)::
(makeTM BR1 EL1 CR1 DL1 BL1 CR1 HR1 AL0 CR0 EL1,RWL 2 2)::
(makeTM BR1 EL1 CR1 DL1 BL1 DR0 CL1 AL0 HR1 CR1,RWL 6 2)::
(makeTM BR1 EL1 CR1 DL1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 EL1 CR1 DR1 BL1 AL1 CL1 CR0 HR1 BL0,RWL 6 2)::
(makeTM BR1 EL1 CR1 DR1 DR0 CL1 AL1 DR1 HR1 CL0,RWL 2 2)::
(makeTM BR1 ER1 BL1 CL0 DR1 CL1 AL1 AR0 HR1 BR0,RWL 3 3)::
(makeTM BR1 ER1 BL1 CL0 DR1 CL1 BR0 AR0 HR1 BR0,RWL 3 3)::
(makeTM BR1 ER1 BL1 CL0 DR1 CL1 CL0 AR0 HR1 DL0,RWL 2 4)::
(makeTM BR1 ER1 BL1 CR0 HR1 DL0 EL1 BR0 AR1 DR1,RWL 5 2)::
(makeTM BR1 ER1 BL1 CL1 AL1 DR0 HR1 CR1 BL0 ER0,RWL 2 2)::
(makeTM BR1 ER1 BL1 CL1 AL1 DR0 HR1 CR1 BR0 ER0,RWL 2 2)::
(makeTM BR1 ER1 BL1 CL1 DR0 CR0 BL1 ER1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 BL1 CL1 DR1 EL1 HR1 AR0 CL1 DL0,RWL 3 3)::
(makeTM BR1 ER1 BL1 CR1 DL0 CR1 AR1 DL1 HR1 BR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 HR1 AR0 DL0 EL1 ER0 CL1 CR1,RWL 5 2)::
(makeTM BR1 ER1 CL0 HR1 AR1 DL1 CL1 AL0 AR0 DR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 AR0 DL1 CR1 AR1 BL0 DR0 HR1,RWL 2 3)::
(makeTM BR1 ER1 CL0 AR1 AR1 DR0 BL1 EL1 HR1 DL0,RWL 6 2)::
(makeTM BR1 ER1 CL0 AR1 CR1 DL0 CL1 BL1 AR0 HR1,RWL 6 2)::
(makeTM BR1 ER1 CL0 AR1 DL0 CL1 AR0 AL1 HR1 DR0,RWL 3 3)::
(makeTM BR1 ER1 CL0 AR1 DL0 CR1 BR1 DL1 HR1 CR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BL0 DL0 CL1 DR1 AR1 HR1 BL0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BL0 DR1 CL1 DR1 AR1 HR1 BL1,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR0 AR0 DL0 CL1 BL1 CR1 HR1,RWL 4 2)::
(makeTM BR1 ER1 CL0 BR0 AR0 DL1 EL1 HR1 CL1 BL0,RWL 3 3)::
(makeTM BR1 ER1 CL0 BR0 AR1 DL1 BL0 CL1 HR1 DR1,RWL 7 2)::
(makeTM BR1 ER1 CL0 BR0 CL1 DL1 ER1 BR0 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR0 CL1 DL1 ER1 BR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL0 BL1 DR1 AL1 AR0 CR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BL1 DR1 AL1 CR1 HR1 EL0 AR0,RWL 6 3)::
(makeTM BR1 ER1 CL0 BR1 HR1 DL1 AR1 DL1 BL1 BR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR1 HR1 DL1 AR1 DL1 BR1 BR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR1 HR1 DL1 AR1 DL1 CL1 BR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR1 HR1 DL1 AR1 DL1 DL1 BR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR1 HR1 DL1 AR1 DL1 DR1 BR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR1 DL0 CL1 DR1 AR0 HR1 BR0,RWL 2 3)::
(makeTM BR1 ER1 CL0 BR1 DL0 CL1 DR1 AR0 HR1 DL0,RWL 2 3)::
(makeTM BR1 ER1 CL0 BR1 DL0 CL1 DR1 AR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BR1 DL1 CL1 AR0 BR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR1 DL1 CL1 AR0 DL0 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 BR1 DL1 CL1 AR1 AL1 HR1 AR0,RWL 4 2)::
(makeTM BR1 ER1 CL0 BR1 DR1 CL1 AR0 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BR1 DR1 CL1 AR1 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BR1 DR1 CL1 AR1 EL0 HR1 BR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BR1 DR1 CL1 BL0 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BR1 DR1 CL1 CL0 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 BR1 DR1 CL1 EL1 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 CR0 AL1 DR0 BL1 ER0 HR1 BL1,RWL 2 3)::
(makeTM BR1 ER1 CL0 CR0 AR1 DL0 AL1 DL1 HR1 BR0,RWL 1 3)::
(makeTM BR1 ER1 CL0 CR0 DL1 AL1 CL1 HR1 BL1 ER0,RWL 2 3)::
(makeTM BR1 ER1 CL0 DL0 BR0 CL1 AR1 DR1 HR1 DR0,RWL 2 2)::
(makeTM BR1 ER1 CL0 DL0 DL0 CL1 DR1 AR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 DL0 DR1 BL1 AR0 CR0 AR1 HR1,RWL 6 2)::
(makeTM BR1 ER1 CL0 DL0 DR1 CL1 AR0 AR1 HR1 BR0,RWL 3 2)::
(makeTM BR1 ER1 CL0 DR0 AL1 CL1 HR1 BR1 AR1 ER1,RWL 2 2)::
(makeTM BR1 ER1 CL0 DR0 AL1 CL1 HR1 BR1 CL0 ER1,RWL 2 2)::
(makeTM BR1 ER1 CL0 DR0 AL1 CL1 HR1 BR1 DL0 ER1,RWL 2 2)::
(makeTM BR1 ER1 CL0 DR1 AL1 CL1 HR1 BR0 AR1 ER1,RWL 2 2)::
(makeTM BR1 ER1 CL0 DR1 AL1 CL1 HR1 BR0 CL0 ER1,RWL 2 2)::
(makeTM BR1 ER1 CL0 EL0 AR0 DL1 CL1 HR1 BL1 BR0,RWL 2 4)::
(makeTM BR1 ER1 CL0 EL0 DL0 CL1 DR1 AR0 HR1 AR1,RWL 2 3)::
(makeTM BR1 ER1 CL0 EL0 DL0 CL1 DR1 AR1 HR1 BL0,RWL 6 2)::
(makeTM BR1 ER1 CL0 ER0 DL1 CL1 AR1 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 ER1 CL0 ER1 DL1 CL1 AR1 DR1 HR1 BR0,RWL 2 2)::
(makeTM BR1 ER1 CR0 HR1 CL1 DL1 AR1 AL0 DL0 AR0,RWL 8 2)::
(makeTM BR1 ER1 CR0 HR1 DR0 AL0 DL1 EL0 BR0 CL0,RWL 4 2)::
(makeTM BR1 ER1 CR0 HR1 DL1 AL0 AR0 CL1 DL0 DR1,RWL 6 3)::
(makeTM BR1 ER1 CR0 HR1 DR1 ER0 DL1 AL0 DL0 AR0,RWL 8 2)::
(makeTM BR1 ER1 CR0 AR0 DL0 AL1 CL1 HR1 AR1 EL0,RWL 15 2)::
(makeTM BR1 ER1 CR0 AR0 DL1 HR1 EL0 BL0 AR1 DL1,RWL 2 2)::
(makeTM BR1 ER1 CR0 AR1 CL1 DR0 HR1 EL0 AL1 CR0,RWL 5 2)::
(makeTM BR1 ER1 CR0 AR1 CL1 DR0 AL1 DL0 HR1 CR0,RWL 5 2)::
(makeTM BR1 ER1 CR0 AR1 DR1 DL0 CL1 BL1 AR0 HR1,RWL 10 2)::
(makeTM BR1 ER1 CR0 BL0 DL1 AR1 BL1 HR1 CL0 EL1,RWL 4 2)::
(makeTM BR1 ER1 CR0 BL0 DL1 CR1 BL1 EL1 HR1 AR0,RWL 9 2)::
(makeTM BR1 ER1 CR0 BR0 CL1 DL1 ER1 BR0 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CR0 BR0 CL1 DL1 ER1 BR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CR0 BR0 DL1 AR0 DL1 BL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CR0 DL0 CL1 AL1 HR1 ER0 AL0 BL0,RWL 2 2)::
(makeTM BR1 ER1 CR0 DL1 CL1 AL1 HR1 ER0 BL0 AL0,RWL 2 2)::
(makeTM BR1 ER1 CR0 DL1 DL1 AL0 BL1 EL1 HR1 AR0,RWL 6 2)::
(makeTM BR1 ER1 CR0 DR1 CL1 AL1 AR0 CL1 HR1 CL0,RWL 5 2)::
(makeTM BR1 ER1 CL1 HR1 AR0 DL0 EL1 BR0 CL1 CR1,RWL 5 2)::
(makeTM BR1 ER1 CL1 HR1 AR0 DL0 EL1 ER0 CL1 CR1,RWL 5 2)::
(makeTM BR1 ER1 CL1 HR1 DL0 CL0 DR1 AR0 AR1 EL0,RWL 2 3)::
(makeTM BR1 ER1 CL1 HR1 DL0 CL1 ER1 DL0 AR1 DR0,RWL 6 3)::
(makeTM BR1 ER1 CL1 HR1 DR0 CL0 BL1 AR1 CR1 CR0,RWL 4 2)::
(makeTM BR1 ER1 CL1 HR1 DL1 CL0 AR0 ER0 CR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 HR1 DL1 CL0 AR1 DL0 DR0 ER0,RWL 28 2)::
(makeTM BR1 ER1 CL1 HR1 DL1 CL1 ER0 DR1 BL1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 AL0 HR1 DL0 AR1 EL1 AR1 CR0,RWL 2 3)::
(makeTM BR1 ER1 CL1 AL0 HR1 DL0 ER0 BL0 AR1 AR0,RWL 16 2)::
(makeTM BR1 ER1 CL1 AL0 HR1 DL0 ER0 BL0 AR1 DR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 AL0 HR1 DL0 ER1 BL0 AR1 AR0,RWL 24 2)::
(makeTM BR1 ER1 CL1 AL0 DL1 CL0 AR0 BL0 DR1 HR1,RWL 6 2)::
(makeTM BR1 ER1 CL1 AR0 HR1 DL1 AL1 BR0 DR0 EL0,RWL 24 2)::
(makeTM BR1 ER1 CL1 AR0 HR1 DL1 AL1 BL1 DR0 EL0,RWL 6 2)::
(makeTM BR1 ER1 CL1 AR0 HR1 DL1 AL1 CR0 DR0 EL0,RWL 19 2)::
(makeTM BR1 ER1 CL1 AR0 AL0 DL1 EL0 HR1 AL1 BL0,RWL 8 2)::
(makeTM BR1 ER1 CL1 AR0 AL1 DL0 BL0 HR1 AR0 BR0,RWL 4 2)::
(makeTM BR1 ER1 CL1 AR0 AL1 DL0 BL0 HR1 AR0 CL1,RWL 4 2)::
(makeTM BR1 ER1 CL1 AR0 AL1 DL0 BL0 HR1 DR1 CL1,RWL 4 2)::
(makeTM BR1 ER1 CL1 AR0 AL1 DL0 CR1 HR1 BR0 EL0,RWL 3 3)::
(makeTM BR1 ER1 CL1 AR0 AL1 DL0 EL0 HR1 BR0 EL0,RWL 3 3)::
(makeTM BR1 ER1 CL1 AR0 AL1 DR0 HR1 BL1 CR0 EL0,RWL 5 3)::
(makeTM BR1 ER1 CL1 AR0 AL1 DL1 BL1 HR1 BR0 EL0,RWL 6 2)::
(makeTM BR1 ER1 CL1 AR0 AL1 DL1 ER1 HR1 BR0 EL0,RWL 3 3)::
(makeTM BR1 ER1 CL1 AR0 BR1 DL1 EL0 HR1 BL0 CR0,RWL 6 2)::
(makeTM BR1 ER1 CL1 AR0 CR0 DL0 EL1 HR1 AL1 BL0,RWL 4 2)::
(makeTM BR1 ER1 CL1 AR0 DL1 CL1 BR1 DR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 AR0 EL1 DL0 EL1 HR1 AL1 BL0,RWL 4 2)::
(makeTM BR1 ER1 CL1 AL1 AR0 DL0 EL0 HR1 BL1 CR0,RWL 6 2)::
(makeTM BR1 ER1 CL1 AL1 DL1 CL1 BR1 DR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 AR1 HR1 DL0 AR1 EL1 CR0 AL0,RWL 4 2)::
(makeTM BR1 ER1 CL1 AR1 HR1 DL1 EL1 DL0 AR0 CR1,RWL 2 3)::
(makeTM BR1 ER1 CL1 AR1 AL1 DL0 BL1 DR0 HR1 BL0,RWL 6 2)::
(makeTM BR1 ER1 CL1 AR1 AL1 DR0 CL0 DL1 HR1 BL0,RWL 3 2)::
(makeTM BR1 ER1 CL1 AR1 AL1 DR0 CL0 DL1 HR1 BR1,RWL 3 2)::
(makeTM BR1 ER1 CL1 AR1 BL1 DR0 HR1 EL0 AL1 CR0,RWL 5 2)::
(makeTM BR1 ER1 CL1 AR1 CR0 DL0 AL1 BR0 HR1 BL0,RWL 3 2)::
(makeTM BR1 ER1 CL1 AR1 CR0 DL0 AL1 BR0 HR1 BR1,RWL 3 2)::
(makeTM BR1 ER1 CL1 AR1 CL1 DR0 HR1 EL0 AL1 CR0,RWL 5 2)::
(makeTM BR1 ER1 CL1 AR1 DL0 DL0 AL1 CR0 HR1 BL0,RWL 3 2)::
(makeTM BR1 ER1 CL1 AR1 DL1 CL1 BR1 DR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL0 DR0 BL0 AR1 CR1 BR0 HR1,RWL 4 3)::
(makeTM BR1 ER1 CL1 BR0 CL1 DL1 AR0 BR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 BR0 CL1 DL1 AR1 BR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 BR0 DL1 DR0 AR1 BL0 HR1 CL0,RWL 4 2)::
(makeTM BR1 ER1 CL1 BL1 HR1 DL0 EL1 AL0 AR0 DR1,RWL 2 4)::
(makeTM BR1 ER1 CL1 BL1 HR1 DL0 ER1 AR0 AR1 CL0,RWL 2 3)::
(makeTM BR1 ER1 CL1 BL1 AR0 DL0 EL1 HR1 CL0 ER0,RWL 10 2)::
(makeTM BR1 ER1 CL1 BL1 AR0 DR0 BL0 DR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL1 AR0 DL1 CL0 BR0 HR1 DR0,RWL 5 3)::
(makeTM BR1 ER1 CL1 BL1 DR0 CR1 AL1 AR0 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL1 DR1 CR1 AL1 AR1 HR1 DR0,RWL 3 2)::
(makeTM BR1 ER1 CL1 BL1 DR1 CR1 BL1 AR0 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL1 DR1 CR1 BL1 AL1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL1 DR1 CR1 BL1 AR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL1 ER0 DR0 BL1 DR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL1 ER0 DR1 BL0 DR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL1 ER1 DR0 BL1 DR1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 BL1 ER1 DR1 BL0 DR1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 BR1 HR1 DL0 EL1 AL0 AR0 BL1,RWL 4 2)::
(makeTM BR1 ER1 CL1 BR1 HR1 DL1 AR1 EL0 BR0 EL1,RWL 2 2)::
(makeTM BR1 ER1 CL1 BR1 AR0 DL0 BR0 DL1 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 CR0 ER1 DR1 HR1 BL0 DL1 AR1,RWL 4 2)::
(makeTM BR1 ER1 CL1 CR1 HR1 DL1 AR1 AL0 BR0 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 CR1 AR0 DL1 CR1 DL0 HR1 AR1,RWL 5 2)::
(makeTM BR1 ER1 CL1 CR1 DL1 CL0 DR1 AR0 BR1 HR1,RWL 3 3)::
(makeTM BR1 ER1 CL1 DL0 AL0 DL1 AR0 BR0 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 DL0 AL1 BL0 DR1 AR1 HR1 BL1,RWL 1 4)::
(makeTM BR1 ER1 CL1 DL0 AL1 BL1 HR1 EL0 CR1 AR0,RWL 4 2)::
(makeTM BR1 ER1 CL1 DL0 AR1 AL1 HR1 BL1 AL0 ER0,RWL 5 2)::
(makeTM BR1 ER1 CL1 DL0 CL1 DL1 AR1 BR0 HR1 CR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DL0 DL1 BL0 AR1 AR0 HR1 AR1,RWL 6 3)::
(makeTM BR1 ER1 CL1 DL0 DR1 BL0 CR0 ER0 AR1 HR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR0 HR1 DL0 AR1 EL1 AR1 CR0,RWL 2 3)::
(makeTM BR1 ER1 CL1 DR0 AL1 BL0 AL0 AR0 HR1 BR1,RWL 4 2)::
(makeTM BR1 ER1 CL1 DR0 AL1 BL1 HR1 CR0 BR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR0 AL1 CL0 AR0 HR1 AR1 EL0,RWL 3 3)::
(makeTM BR1 ER1 CL1 DR0 DR1 BL0 BL1 AR1 HR1 DR0,RWL 6 3)::
(makeTM BR1 ER1 CL1 DL1 DR0 BL0 AR1 CR1 AR0 HR1,RWL 4 3)::
(makeTM BR1 ER1 CL1 DR1 HR1 DL0 AR1 AL0 EL1 CR0,RWL 1 4)::
(makeTM BR1 ER1 CL1 DR1 HR1 DL0 AR1 EL1 BR0 CR0,RWL 1 4)::
(makeTM BR1 ER1 CL1 DR1 AL0 AL1 HR1 CR0 DL0 AL0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 AL0 DL0 AR1 AL1 HR1 CR0,RWL 1 3)::
(makeTM BR1 ER1 CL1 DR1 AL1 BL1 AR1 BR0 HR1 CL0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 AL0 CR0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 BR1 BL0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 BR1 BR0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 BR1 BL1 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 BR1 CL0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 BR1 CR0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 BR1 CL1 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 CR0 BL0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 CR0 BR0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 CR0 CL0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 CL1 AL1 HR1 CR0 CR0 ER0,RWL 2 2)::
(makeTM BR1 ER1 CL1 DR1 DL0 BL0 AR0 CL0 BR0 HR1,RWL 4 3)::
(makeTM BR1 ER1 CL1 DR1 DL0 CL0 AL1 AR0 HR1 BL1,RWL 2 2)::
(makeTM BR1 ER1 CL1 EL0 AR0 DL0 BL1 HR1 AR1 AR0,RWL 1 4)::
(makeTM BR1 ER1 CL1 EL0 DL0 BL1 AR0 CL0 HR1 DR0,RWL 5 2)::
(makeTM BR1 ER1 CL1 ER0 HR1 DL0 EL0 DL1 AR1 BL0,RWL 11 2)::
(makeTM BR1 ER1 CL1 ER0 DR0 CL0 AL1 HR1 BL1 AR1,RWL 3 3)::
(makeTM BR1 ER1 CL1 ER0 DL1 CL1 AL1 DR1 HR1 BR1,RWL 2 2)::
(makeTM BR1 ER1 CL1 ER0 DR1 CL0 ER0 HR1 BL1 AR1,RWL 3 3)::
(makeTM BR1 ER1 CL1 ER1 HR1 DL0 AR1 AL0 EL1 CR0,RWL 3 2)::
(makeTM BR1 ER1 CL1 ER1 CL1 DL1 BR0 DR0 HR1 AR1,RWL 2 2)::
(makeTM BR1 ER1 CR1 HR1 DR1 AR1 EL1 EL0 AR0 DL0,RWL 4 3)::
(makeTM BR1 ER1 CR1 HR1 DR1 DL0 EL1 CR0 CL0 AR0,RWL 4 2)::
(makeTM BR1 ER1 CR1 AL0 DL1 ER0 BL1 DL0 BR0 HR1,RWL 28 2)::
(makeTM BR1 ER1 CR1 AR1 CL1 DR0 HR1 EL0 AL1 CR0,RWL 5 2)::
(makeTM BR1 ER1 CR1 AR1 CL1 DR0 AL1 DL0 HR1 CR0,RWL 5 2)::
(makeTM BR1 ER1 CR1 AR1 DL1 CL1 AR0 DL0 HR1 DR0,RWL 4 2)::
(makeTM BR1 ER1 CR1 BL0 DR0 AR1 DL1 BL1 HR1 CR0,RWL 12 2)::
(makeTM BR1 ER1 CR1 BL0 DL1 HR1 AR1 DL1 BL1 AR1,RWL 4 3)::
(makeTM BR1 ER1 CR1 BL0 DL1 DR0 AR1 BL1 HR1 CL0,RWL 4 3)::
(makeTM BR1 ER1 CR1 BR0 DL1 AR0 AL0 CL0 DL1 HR1,RWL 4 2)::
(makeTM BR1 ER1 CR1 BL1 DR0 ER0 AL1 DR1 HR1 BL0,RWL 2 2)::
(makeTM BR1 ER1 CR1 BR1 DL0 AL1 HR1 CL1 DL1 AR0,RWL 6 3)::
(makeTM BR1 ER1 CR1 BR1 DL1 AR0 BR1 CL1 HR1 DL0,RWL 6 2)::
(makeTM BR1 ER1 CR1 BR1 DL1 ER0 BL1 DL1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CR1 BR1 DL1 EL1 BL1 DL1 HR1 AR0,RWL 2 2)::
(makeTM BR1 ER1 CR1 DR0 DL1 BR1 HR1 AL0 EL0 BL1,RWL 3 2)::
(makeTM BR1 ER1 CR1 DL1 BL0 EL1 HR1 BL1 ER0 AL0,RWL 2 2)::
(makeTM BR1 ER1 CR1 DR1 DL1 AL1 AR0 CL1 HR1 CL0,RWL 5 2)::
(makeTM BR1 ER1 CR1 DR1 DL1 BR0 AR1 CL0 DR1 HR1,RWL 2 3)::
(makeTM BR1 ER1 CR1 EL0 DL0 AR0 HR1 CL1 AL1 BL1,RWL 4 3)::
(makeTM BR1 ER1 CR1 EL0 DL1 AL0 HR1 BL0 AR1 CL0,RWL 2 3)::
(makeTM BR1 ER1 CR1 EL0 DL1 AR1 DR1 CL0 HR1 BR0,RWL 4 2)::
nil.


Definition tm_NG0:list ((TM Σ)*(DeciderType)) :=
(makeTM BR0 HR1 AL1 CL1 DR1 DL0 BL1 ER1 CL1 ER0,NG 0 11)::
(makeTM BR0 HR1 CL0 BR0 BR1 DL1 ER1 DL0 CL1 ER0,NG 0 1)::
(makeTM BR0 HR1 CL0 BR0 DL0 DL1 BR1 ER1 CL1 ER0,NG 0 1)::
(makeTM BR0 HR1 CL0 BR0 DL1 ER1 BR1 DL0 CL1 ER0,NG 0 1)::
(makeTM BR0 HR1 CL0 BL1 DR0 BL0 ER0 ER1 CL1 DR1,NG 0 1)::
(makeTM BR0 HR1 CL0 BR1 DL1 DL0 ER0 BR0 CL1 ER1,NG 0 1)::
(makeTM BR0 HR1 CL0 BR1 DR1 EL0 BL1 AR1 AR0 CL1,NG 0 2)::
(makeTM BR0 HR1 CL0 CL1 DR0 BL0 ER0 DR1 BL1 ER1,NG 0 1)::
(makeTM BR0 HR1 CL0 DL0 DL1 BR0 ER0 CL1 BR1 ER1,NG 0 1)::
(makeTM BR0 HR1 CL0 DR1 DR0 BL0 ER0 ER1 CL1 BL1,NG 0 1)::
(makeTM BR0 HR1 CL0 EL0 DR1 EL0 BR1 AR1 AR0 CL1,NG 0 2)::
(makeTM BR0 HR1 CL0 ER0 DL0 AL0 ER1 DL1 AR1 CR0,NG 0 3)::
(makeTM BR0 HR1 CL0 ER0 DL0 CL0 ER1 DL1 AR1 CR0,NG 0 3)::
(makeTM BR0 HR1 CL0 ER0 DL0 CL1 ER1 DL1 BR0 BR1,NG 0 1)::
(makeTM BR0 HR1 CL0 ER0 DL0 DL1 BR1 CL1 BR0 ER1,NG 0 1)::
(makeTM BR0 HR1 CL0 ER1 DL1 CL1 ER0 BR0 BR1 DL0,NG 0 1)::
(makeTM BR0 HR1 CR0 AR0 DL0 AL0 EL0 BR1 BR1 DL1,NG 0 2)::
(makeTM BR0 HR1 CR0 AR0 DL0 CR0 EL0 BR1 BR1 DL1,NG 0 2)::
(makeTM BR0 HR1 CR0 AR0 DL0 EL0 EL0 BR1 BR1 DL1,NG 0 2)::
(makeTM BR0 HR1 CR0 BL0 BL1 DR1 EL1 DR0 CR1 EL0,NG 0 1)::
(makeTM BR0 HR1 CR0 BL0 DR0 DR1 BL1 EL1 CR1 EL0,NG 0 1)::
(makeTM BR0 HR1 CR0 BL0 DR1 EL1 BL1 DR0 CR1 EL0,NG 0 1)::
(makeTM BR0 HR1 CR0 BL1 DR1 DR0 EL0 BL0 CR1 EL1,NG 0 1)::
(makeTM BR0 HR1 CR0 BR1 DL0 BR0 EL0 EL1 CR1 DL1,NG 0 1)::
(makeTM BR0 HR1 CR0 CR1 DL0 BR0 EL0 DL1 BR1 EL1,NG 0 1)::
(makeTM BR0 HR1 CR0 DR0 DR1 BL0 EL0 CR1 BL1 EL1,NG 0 1)::
(makeTM BR0 HR1 CR0 DL1 DL0 BR0 EL0 EL1 CR1 BR1,NG 0 1)::
(makeTM BR0 HR1 CR0 EL0 DR0 CR1 EL1 DR1 BL0 BL1,NG 0 1)::
(makeTM BR0 HR1 CR0 EL0 DR0 DR1 BL1 CR1 BL0 EL1,NG 0 1)::
(makeTM BR0 HR1 CR0 EL1 BL1 DR1 BL0 DR0 CR1 EL0,NG 0 1)::
(makeTM BR0 HR1 CR0 EL1 DR1 CR1 EL0 BL0 BL1 DR0,NG 0 1)::
(makeTM BR0 HR1 CL1 BL0 DL1 CR0 ER1 DL0 AR1 CR1,NG 0 3)::
(makeTM BR0 HR1 CL1 BR0 DL0 AR1 EL1 AR0 CR1 CL0,NG 0 2)::
(makeTM BR0 HR1 CL1 BR0 DL0 AR1 EL1 DR1 CR1 CL0,NG 0 2)::
(makeTM BR0 HR1 CL1 BR0 DL1 CR0 ER1 DL0 AR1 CR1,NG 0 3)::
(makeTM BR0 HR1 CL1 BR0 DR1 CL0 AR1 EL1 CR1 EL1,NG 0 2)::
(makeTM BR0 HR1 CL1 BR0 DR1 DL0 EL1 BR1 AL0 CL1,NG 0 11)::
(makeTM BR0 HR1 CL1 BR0 DR1 DL0 EL1 BR1 AL0 CR1,NG 0 11)::
(makeTM BR0 HR1 CL1 BR0 DR1 DL0 EL1 BR1 AL0 DL0,NG 0 11)::
(makeTM BR0 HR1 CL1 BL1 DR0 ER0 ER1 CL0 BL0 DR1,NG 0 1)::
(makeTM BR0 HR1 CL1 BR1 DL0 DL1 ER0 CL0 BR0 ER1,NG 0 1)::
(makeTM BR0 HR1 CL1 BR1 DL0 ER1 DR1 CL0 BR0 AR0,NG 0 5)::
(makeTM BR0 HR1 CL1 BR1 DL1 DL0 EL0 AR0 AR0 CL0,NG 0 3)::
(makeTM BR0 HR1 CL1 DR1 BR0 CL0 EL1 DR0 BR1 EL0,NG 0 1)::
(makeTM BR0 HR1 CL1 EL0 DL0 AR1 EL1 AR0 CR1 CL0,NG 0 2)::
(makeTM BR0 HR1 CL1 EL0 DR1 CR1 AL1 DR0 BL1 EL1,NG 0 4)::
(makeTM BR0 HR1 CL1 ER0 DL0 AR1 DR1 CL0 BL0 AL1,NG 0 2)::
(makeTM BR0 HR1 CL1 ER1 DL0 EL1 AR1 BR0 CL0 DL1,NG 0 6)::
(makeTM BR0 HR1 CR1 AR0 DL0 CR1 AR1 EL1 CL0 BR1,NG 0 2)::
(makeTM BR0 HR1 CR1 BL0 DR0 AR0 ER1 EL0 BL1 BR1,NG 0 3)::
(makeTM BR0 HR1 CR1 BR0 DL0 BR0 EL1 DR1 AL0 CL1,NG 0 12)::
(makeTM BR0 HR1 CR1 BL1 DR0 DR1 EL0 CR0 BL0 EL1,NG 0 1)::
(makeTM BR0 HR1 CR1 BL1 DL1 AR1 EL0 DL0 AR1 CR1,NG 0 12)::
(makeTM BR0 HR1 CR1 BR1 DL0 EL0 EL1 CR0 BR0 DL1,NG 0 1)::
(makeTM BR0 HR1 CR1 BR1 DL1 DR0 AL1 EL0 DL0 EL1,NG 0 3)::
(makeTM BR0 HR1 CR1 CR0 DL0 EL0 BR1 DL1 BR0 EL1,NG 0 1)::
(makeTM BR0 HR1 CR1 DL0 DL1 AR1 ER0 EL0 BL1 EL0,NG 0 12)::
(makeTM BR0 HR1 CR1 DL0 DR1 AR0 BL1 EL0 DL0 AR0,NG 0 7)::
(makeTM BR0 HR1 CR1 DR0 DL1 BR1 AL0 EL0 DL1 EL1,NG 0 3)::
(makeTM BR0 HR1 CR1 DL1 BL0 CR0 ER1 DL0 BL1 ER0,NG 0 1)::
(makeTM BR0 HR1 CR1 DL1 DL1 AR1 ER0 DL0 CL0 BL1,NG 0 12)::
(makeTM BR0 HR1 CR1 DR1 DL1 AR1 EL0 CL0 BR1 EL1,NG 0 3)::
(makeTM BR0 HR1 CR1 EL0 DL1 AR1 BL1 DL0 DR0 DL0,NG 0 12)::
(makeTM BR0 HR1 CR1 ER0 DL1 AR1 BL1 DL0 DL0 BL0,NG 0 4)::
(makeTM BR0 HR1 CR1 EL1 DL1 AR1 BL1 DL0 CR1 DR1,NG 0 12)::
(makeTM BR0 AL0 AL1 CR1 AL1 DR1 EL0 BR1 HR1 DL1,NG 0 2)::
(makeTM BR0 AL0 AL1 CR1 DL0 DR1 EL0 BR1 HR1 CL1,NG 0 2)::
(makeTM BR0 AL0 AL1 CR1 DL0 DR1 EL0 BR1 HR1 DL1,NG 0 2)::
(makeTM BR0 AL0 AL1 CR1 DL1 CR0 BR1 DL0 HR1 HR1,NG 0 1)::
(makeTM BR0 AL0 AL1 CR1 DR1 DL1 EL0 BR1 HR1 DL0,NG 0 2)::
(makeTM BR0 AL0 CL0 DL1 AL1 ER1 CR1 AL1 DR0 HR1,NG 0 12)::
(makeTM BR0 AL0 CL0 DR1 AL1 CR1 ER0 HR1 BR1 EL1,NG 0 12)::
(makeTM BR0 AL0 CL0 EL1 DR1 ER0 EL1 HR1 CR1 AL1,NG 0 11)::
(makeTM BR0 AL0 CR0 HR1 DR1 CR1 EL1 DL1 BL1 AL0,NG 0 2)::
(makeTM BR0 AL0 CR0 CL0 DR1 HR1 ER0 DR0 EL1 AL1,NG 0 4)::
(makeTM BR0 AL0 CR0 CR1 AL1 DL1 BR1 DL0 HR1 HR1,NG 0 1)::
(makeTM BR0 AL0 CL1 HR1 DR1 AL1 BR1 ER0 DL0 CR1,NG 0 12)::
(makeTM BR0 AL0 CL1 HR1 DR1 AL1 BR1 ER0 EL1 CR1,NG 0 12)::
(makeTM BR0 AL0 CL1 DL0 DR1 AR1 EL1 CR0 HR1 BL1,NG 0 3)::
(makeTM BR0 AL0 CL1 DR0 AL1 DL1 HR1 ER1 BR0 CR1,NG 0 4)::
(makeTM BR0 AL0 CL1 DR1 AL1 CR0 CR1 EL0 HR1 DL1,NG 0 2)::
(makeTM BR0 AL0 CR1 HR1 AL1 DR1 ER0 CR1 EL0 CL1,NG 0 3)::
(makeTM BR0 AL0 CR1 HR1 DR0 EL1 DL1 CR0 AL0 BL0,NG 0 2)::
(makeTM BR0 AL0 CR1 AL0 DL1 AR0 BL1 EL0 CL1 HR1,NG 0 5)::
(makeTM BR0 AL0 CR1 CR1 DL1 AR0 BL1 EL0 CL1 HR1,NG 0 5)::
(makeTM BR0 AL0 CR1 DR0 DL1 HR1 EL0 DL1 AR1 AL0,NG 0 12)::
(makeTM BR0 AL0 CR1 DL1 DR0 EL1 ER1 HR1 CL0 AR1,NG 0 10)::
(makeTM BR0 AL0 CR1 ER0 CL0 DL1 AL1 DR1 HR1 AR1,NG 0 4)::
(makeTM BR0 AR0 CL0 AR1 DL1 ER0 BR1 BL0 CR1 HR1,NG 0 2)::
(makeTM BR0 AR0 CL1 BR1 DL0 AR1 ER1 CL0 DR1 HR1,NG 0 5)::
(makeTM BR0 AR0 CL1 BR1 DL1 AL0 EL0 HR1 AR0 CL0,NG 0 3)::
(makeTM BR0 AL1 CL0 DR0 AL1 EL1 BR1 CL0 CL1 HR1,NG 0 2)::
(makeTM BR0 AL1 CR0 ER1 DL0 AL0 EL1 HR1 BR1 CL0,NG 0 3)::
(makeTM BR0 AL1 CL1 DR0 AR1 EL1 EL0 BR1 AL0 HR1,NG 0 2)::
(makeTM BR0 AL1 CR1 CR0 DL0 AL0 BR1 DL1 HR1 HR1,NG 0 1)::
(makeTM BR0 AL1 CR1 CR1 DL1 AR0 BL1 EL0 CL1 HR1,NG 0 5)::
(makeTM BR0 AR1 CL0 ER0 DL1 HR1 EL0 BL1 AR1 AL0,NG 0 4)::
(makeTM BR0 AR1 CL0 ER1 DL1 DL0 AR1 BL0 AR0 HR1,NG 0 2)::
(makeTM BR0 AR1 CL1 AR0 DL1 HR1 AR0 EL0 CL0 AL0,NG 0 5)::
(makeTM BR0 AR1 CL1 BL1 DL1 EL0 AR0 CR1 HR1 DL0,NG 0 3)::
(makeTM BR0 AR1 CL1 CR0 DL0 AL1 EL1 AL0 AR1 HR1,NG 0 12)::
(makeTM BR0 AR1 CL1 CR0 DL0 AL1 EL1 AL0 CR1 HR1,NG 0 12)::
(makeTM BR0 AR1 CL1 CR0 DL0 CR0 EL1 AL0 AR1 HR1,NG 0 12)::
(makeTM BR0 AR1 CL1 CR1 DL1 EL1 AR0 BL1 HR1 DL0,NG 0 3)::
(makeTM BR0 AR1 CL1 ER1 DL1 AL0 AR1 DL0 HR1 CR0,NG 0 3)::
(makeTM BR0 AR1 CL1 ER1 DL1 AR0 AR1 DL0 HR1 CR0,NG 0 3)::
(makeTM BR0 AR1 CR1 AR0 DL0 HR1 EL1 DL1 BR1 BL0,NG 0 3)::
(makeTM BR0 AR1 CR1 BL0 DL1 DR1 HR1 EL1 BL1 AR0,NG 0 3)::
(makeTM BR0 AR1 CR1 ER0 DL0 CL0 AR1 CL1 DL1 HR1,NG 0 2)::
(makeTM BR0 AR1 CR1 ER1 DL0 CL0 AR1 CL1 AL1 HR1,NG 0 2)::
(makeTM BR0 AR1 CR1 ER1 DL0 CL0 ER0 CL1 AR1 HR1,NG 0 2)::
(makeTM BR0 BL0 CL1 BL0 DR1 AL0 AL1 ER1 CR0 HR1,NG 0 12)::
(makeTM BR0 BL0 CL1 BL0 DR1 AL0 BL1 ER1 CR0 HR1,NG 0 12)::
(makeTM BR0 BL0 CR1 HR1 DR0 CR0 DL1 EL1 AR0 EL0,NG 0 4)::
(makeTM BR0 BL0 CR1 ER1 DL0 CL0 ER0 CL1 AR1 HR1,NG 0 2)::
(makeTM BR0 BL1 CR1 AL0 DL1 DR0 ER1 CL1 HR1 AR1,NG 0 5)::
(makeTM BR0 BL1 CR1 BL0 DR1 HR1 ER0 DR0 EL1 AR1,NG 0 3)::
(makeTM BR0 BL1 CR1 ER1 DL1 CL0 AL1 CL1 HR1 AR1,NG 0 11)::
(makeTM BR0 BL1 CR1 ER1 DL1 CL0 AR1 CL1 HR1 AR1,NG 0 11)::
(makeTM BR0 BL1 CR1 ER1 DL1 CL0 ER1 CL1 HR1 AR1,NG 0 11)::
(makeTM BR0 BR1 CL0 AR0 DL0 CL1 AR1 DL1 HR1 HR1,NG 0 1)::
(makeTM BR0 BR1 CR0 DL1 DL0 ER1 EL1 HR1 AR1 EL0,NG 0 4)::
(makeTM BR0 BR1 CL1 AR1 DL1 CL0 EL0 CL0 AL1 HR1,NG 0 3)::
(makeTM BR0 BR1 CR1 EL1 DR1 CL0 AL1 AR0 HR1 CL1,NG 0 12)::
(makeTM BR0 BR1 CR1 EL1 DR1 CL0 EL1 AR0 HR1 CL1,NG 0 12)::
(makeTM BR0 CL0 CL0 ER0 DL0 HR1 ER1 DL1 AR1 AR0,NG 0 3)::
(makeTM BR0 CL0 CL1 AR0 DR0 EL1 EL0 BR1 BL1 HR1,NG 0 2)::
(makeTM BR0 CL0 CL1 BR0 DL1 DR1 AR1 EL0 HR1 AL0,NG 0 3)::
(makeTM BR0 CL0 CL1 BR1 DL0 AL1 DR1 ER0 BR1 HR1,NG 0 4)::
(makeTM BR0 CL0 CR1 HR1 DR1 CL1 ER0 AR0 EL1 AL0,NG 0 3)::
(makeTM BR0 CR0 CL0 BR0 DL1 HR1 EL0 AR1 ER1 DL0,NG 0 2)::
(makeTM BR0 CR0 CR0 DL1 DL1 BR1 AL0 EL0 DL0 HR1,NG 0 2)::
(makeTM BR0 CR0 CR1 AL0 DL0 BR1 AL1 DL1 HR1 HR1,NG 0 1)::
(makeTM BR0 CR0 CR1 BR0 DL1 AL0 BR1 EL1 CL0 HR1,NG 0 4)::
(makeTM BR0 CL1 AL1 BR1 DR0 AL0 HR1 ER1 CR1 EL1,NG 0 3)::
(makeTM BR0 CL1 AL1 BR1 DL1 EL0 BL1 HR1 BL0 AR0,NG 0 7)::
(makeTM BR0 CL1 CL0 AR0 DL0 DL1 BR1 AR1 HR1 HR1,NG 0 1)::
(makeTM BR0 CL1 CL0 DR1 DL1 HR1 AL1 ER0 DR0 AL0,NG 0 2)::
(makeTM BR0 CL1 CL0 DR1 DL1 HR1 ER1 DL0 AR0 AR1,NG 0 4)::
(makeTM BR0 CL1 CR0 BR1 DL1 DR1 AL1 EL1 HR1 AL0,NG 0 3)::
(makeTM BR0 CL1 CL1 AR1 DL0 EL0 AR0 BR0 CL0 HR1,NG 0 2)::
(makeTM BR0 CL1 CL1 AR1 DL0 EL0 AR0 DL0 CL0 HR1,NG 0 2)::
(makeTM BR0 CL1 CL1 AR1 DL0 EL0 AR0 ER0 CL0 HR1,NG 0 2)::
(makeTM BR0 CL1 CL1 BR1 DR1 DL1 ER1 CL0 HR1 AR1,NG 0 2)::
(makeTM BR0 CL1 CL1 DR0 AL1 EL1 HR1 AR1 BR1 EL0,NG 0 3)::
(makeTM BR0 CL1 CR1 HR1 DL1 CR0 EL0 EL1 AL0 BR1,NG 0 4)::
(makeTM BR0 CL1 CR1 HR1 DR1 EL0 AL0 BR1 CL0 DR0,NG 0 2)::
(makeTM BR0 CL1 CR1 DL1 AL1 AL0 DR1 ER0 HR1 BR1,NG 0 2)::
(makeTM BR0 CL1 CR1 DL1 BL1 ER0 AL0 CL1 HR1 AR1,NG 0 3)::
(makeTM BR0 CR1 CR0 AR1 DL1 EL0 EL0 HR1 BR1 AL1,NG 0 8)::
(makeTM BR0 CR1 CL1 AR1 DR1 EL0 BR1 BL1 HR1 AL1,NG 0 2)::
(makeTM BR0 CR1 CR1 AL0 DL1 AR0 BL1 EL0 CL1 HR1,NG 0 5)::
(makeTM BR0 DL0 CR0 BR1 DL1 CR1 AL0 AL1 HR1 HR1,NG 0 1)::
(makeTM BR0 DL0 CR0 ER0 DL1 CR1 EL1 BL0 AL0 HR1,NG 0 3)::
(makeTM BR0 DL0 CR1 HR1 DR0 AR1 EL1 ER0 AL0 EL1,NG 0 4)::
(makeTM BR0 DL0 CR1 BL1 AL1 AR0 EL1 HR1 BL1 EL0,NG 0 2)::
(makeTM BR0 DR0 CL0 DR0 AL1 EL1 BR1 CL0 CL1 HR1,NG 0 2)::
(makeTM BR0 DR0 CL1 BR1 AL1 AL0 ER1 CL0 HR1 BR0,NG 0 2)::
(makeTM BR0 DR0 CL1 BR1 DL1 AL0 EL0 HR1 AR0 CL0,NG 0 3)::
(makeTM BR0 DR0 CL1 CL0 AR1 BL1 EL1 CR1 DL1 HR1,NG 0 2)::
(makeTM BR0 DR0 CL1 DR0 AL1 EL1 EL0 BR1 AL0 HR1,NG 0 2)::
(makeTM BR0 DR0 CL1 ER1 AR1 CL0 BL1 AR1 HR1 CR1,NG 0 5)::
(makeTM BR0 DL1 CL0 HR1 DR1 CL0 EL1 ER0 AR1 CL1,NG 0 11)::
(makeTM BR0 DL1 CR0 HR1 DL0 AL0 ER1 AL0 CR1 BR1,NG 0 2)::
(makeTM BR0 DL1 CR0 HR1 DL0 CR1 ER1 AL0 CL1 BR1,NG 0 2)::
(makeTM BR0 DL1 CL1 BR1 AL1 AR0 EL0 HR1 CR1 EL1,NG 0 4)::
(makeTM BR0 DL1 CR1 BL1 AL0 CR0 EL0 HR1 AL1 ER1,NG 0 12)::
(makeTM BR0 DL1 CR1 BL1 AL1 AR0 EL0 HR1 AR1 EL0,NG 0 2)::
(makeTM BR0 DL1 CR1 BR1 DL0 AL0 AL1 CR0 HR1 HR1,NG 0 1)::
(makeTM BR0 DL1 CR1 CL1 AL0 ER0 ER1 AL1 HR1 BR1,NG 0 3)::
(makeTM BR0 DL1 CR1 EL0 AL1 AR0 AL0 DL0 BL1 HR1,NG 0 2)::
(makeTM BR0 DL1 CR1 ER0 AL1 EL0 AR1 DL0 HR1 DR1,NG 0 4)::
(makeTM BR0 DL1 CR1 ER1 AL1 AR0 AR1 DL0 HR1 AR1,NG 0 4)::
(makeTM BR0 DL1 CR1 ER1 AL1 AR0 AR1 DL0 HR1 DL0,NG 0 4)::
(makeTM BR0 DL1 CR1 ER1 DR1 AL0 AL1 CR0 HR1 CR1,NG 0 2)::
(makeTM BR0 DR1 CL0 HR1 DL1 CL0 ER0 CL0 AR1 EL1,NG 0 12)::
(makeTM BR0 DR1 CL0 HR1 DR1 CL0 EL1 ER0 AR1 CL1,NG 0 11)::
(makeTM BR0 DR1 CL0 DR1 DL1 AR1 CR1 EL0 HR1 BL1,NG 0 3)::
(makeTM BR0 DR1 CL0 EL0 DL1 HR1 AR1 BL0 AR0 EL1,NG 0 3)::
(makeTM BR0 DR1 CR0 BR1 DL1 CL1 AL1 EL0 HR1 AL0,NG 0 3)::
(makeTM BR0 DR1 CL1 HR1 AR1 CL0 EL1 ER0 BL1 DR0,NG 0 4)::
(makeTM BR0 DR1 CL1 BR1 AR1 EL0 CL1 HR1 CL0 ER0,NG 0 3)::
(makeTM BR0 DR1 CL1 CR0 DL0 CL1 ER0 BL0 AR1 HR1,NG 0 4)::
(makeTM BR0 DR1 CL1 DL0 DR1 HR1 BL1 ER1 AL0 ER0,NG 0 11)::
(makeTM BR0 DR1 CR1 DR0 AL1 HR1 EL0 DL1 AR1 AL0,NG 0 12)::
(makeTM BR0 DR1 CR1 DR0 DL1 HR1 EL0 DL1 AR1 AL0,NG 0 12)::
(makeTM BR0 DR1 CR1 EL1 AL0 CR0 BL1 CR1 DL0 HR1,NG 0 12)::
(makeTM BR0 EL0 AL1 CR0 DL1 AL1 ER1 HR1 CL1 BR1,NG 0 11)::
(makeTM BR0 EL0 CL0 DR1 AL1 AR1 EL1 BR1 HR1 CL1,NG 0 3)::
(makeTM BR0 EL0 CR0 BR1 DL1 BR0 AL1 HR1 DL0 BL0,NG 0 5)::
(makeTM BR0 EL0 CL1 BR1 DL1 CR0 EL1 HR1 AL1 EL0,NG 0 2)::
(makeTM BR0 EL0 CL1 CR0 DL1 AL1 ER1 HR1 CL1 BR1,NG 0 11)::
(makeTM BR0 EL0 CR1 AR0 DL1 BR0 BL1 EL0 CL0 HR1,NG 0 7)::
(makeTM BR0 EL0 CR1 BL0 DR1 DR1 AL1 AR1 HR1 DL1,NG 0 3)::
(makeTM BR0 EL0 CR1 BR0 DL1 HR1 AL1 DR1 DL1 AL0,NG 0 4)::
(makeTM BR0 EL0 CR1 BL1 DR0 AR1 EL0 HR1 AL1 EL0,NG 0 12)::
(makeTM BR0 EL0 CR1 BL1 DR1 DR1 AL1 AR1 HR1 DL1,NG 0 3)::
(makeTM BR0 ER0 CL0 HR1 DL1 AL0 AR1 CL1 AR1 ER1,NG 0 3)::
(makeTM BR0 ER0 CL0 HR1 DL1 AL0 ER1 CL1 AR1 ER1,NG 0 3)::
(makeTM BR0 ER0 CL0 HR1 DR1 CL0 EL1 ER0 AR1 CL1,NG 0 11)::
(makeTM BR0 ER0 CL0 DL0 DL0 AR1 AR1 CL1 AR0 HR1,NG 0 2)::
(makeTM BR0 ER0 CL0 EL0 DL0 AR1 AR1 CL1 AR0 HR1,NG 0 2)::
(makeTM BR0 ER0 CR0 DL1 DL1 BR1 AL0 EL0 DL0 HR1,NG 0 2)::
(makeTM BR0 ER0 CL1 BR1 DL0 AR1 DR1 CL0 BR0 HR1,NG 0 5)::
(makeTM BR0 ER0 CR1 HR1 DL0 DL1 ER1 CL1 AR1 ER0,NG 0 3)::
(makeTM BR0 ER0 CR1 HR1 DL1 AR0 AL0 CL1 DL0 ER1,NG 0 3)::
(makeTM BR0 ER0 CR1 AL0 DR1 BL0 EL1 HR1 BL1 ER1,NG 0 3)::
(makeTM BR0 ER0 CR1 BL1 DL1 AR1 AL1 DL0 HR1 BL0,NG 0 12)::
(makeTM BR0 ER0 CR1 CL1 DL1 AR0 BL1 DL0 HR1 BR0,NG 0 4)::
(makeTM BR0 EL1 CL1 AR0 DL1 CR0 AL1 HR1 BR1 EL0,NG 0 2)::
(makeTM BR0 EL1 CL1 DR1 AL1 CL0 AR1 CL1 HR1 BR1,NG 0 3)::
(makeTM BR0 EL1 CR1 HR1 DR0 CR0 DL1 AR1 BR1 EL0,NG 0 3)::
(makeTM BR0 EL1 CR1 AR1 DL1 CL0 AL1 CL1 HR1 BR1,NG 0 3)::
(makeTM BR0 EL1 CR1 BL1 DL1 AR1 AL1 DL0 HR1 DR1,NG 0 3)::
(makeTM BR0 EL1 CR1 DR0 DL1 CR0 AL1 BL1 DL0 HR1,NG 0 9)::
(makeTM BR0 EL1 CR1 DR1 DR0 EL0 AL1 CR0 DL1 HR1,NG 0 2)::
(makeTM BR0 ER1 CL1 HR1 DL0 CL0 DR1 AL1 BL1 ER0,NG 0 3)::
(makeTM BR0 ER1 CL1 BR0 DR1 CL0 AR1 DL1 HR1 CL1,NG 0 2)::
(makeTM BR0 ER1 CL1 DL0 DL0 HR1 AR1 EL1 AR0 BR1,NG 0 8)::
(makeTM BR0 ER1 CR1 AL0 DR0 EL1 DL1 CR0 BL0 HR1,NG 0 2)::
(makeTM BR0 ER1 CR1 CL1 DL1 AR0 BL1 DL0 HR1 CL0,NG 0 4)::
(makeTM BR1 HR1 BL1 CL0 DL1 AR0 ER1 EL0 CL0 AR1,NG 0 2)::
(makeTM BR1 HR1 BL1 CR0 DL1 CR1 EL1 EL0 AR1 EL0,NG 0 2)::
(makeTM BR1 HR1 BL1 CR0 DL1 DR1 EL1 DR1 AR1 EL0,NG 0 2)::
(makeTM BR1 HR1 CL0 BR0 BR1 DL1 ER1 DL0 CL1 ER0,NG 0 1)::
(makeTM BR1 HR1 CL0 BL1 DR0 BL0 ER0 ER1 CL1 DR1,NG 0 1)::
(makeTM BR1 HR1 CL0 CL1 DR1 BL1 ER1 DR0 AR0 DR0,NG 0 3)::
(makeTM BR1 HR1 CL0 DL0 DL1 BR0 ER0 CL1 BR1 ER1,NG 0 1)::
(makeTM BR1 HR1 CL0 DL1 AL1 DL0 ER0 DR1 BL1 BR0,NG 0 12)::
(makeTM BR1 HR1 CL0 DR1 AL1 BL1 ER1 DL1 AL0 ER0,NG 0 4)::
(makeTM BR1 HR1 CL0 DR1 DR0 BL0 ER0 ER1 CL1 BL1,NG 0 1)::
(makeTM BR1 HR1 CL0 ER1 AL1 DL1 CL0 DL1 BR1 ER0,NG 0 11)::
(makeTM BR1 HR1 CL0 ER1 DL0 CL1 AL1 BR1 BR1 ER0,NG 0 11)::
(makeTM BR1 HR1 CL0 ER1 DR1 BL0 AR1 DL0 CL1 ER0,NG 0 2)::
(makeTM BR1 HR1 CR0 AR0 DL1 DR0 EL0 BL0 BR1 CL0,NG 0 4)::
(makeTM BR1 HR1 CR0 BL0 DR0 EL1 CL1 DR1 AL1 BR1,NG 0 3)::
(makeTM BR1 HR1 CR0 BR0 CL1 DL1 EL0 AR0 ER1 DL0,NG 0 6)::
(makeTM BR1 HR1 CR0 BR0 CL1 DL1 ER0 DL0 AR0 AL0,NG 0 4)::
(makeTM BR1 HR1 CR0 BR0 CL1 DR1 HR1 EL1 AR1 EL0,NG 0 3)::
(makeTM BR1 HR1 CR0 BR1 DL1 CL0 EL1 BR0 AR1 EL0,NG 0 2)::
(makeTM BR1 HR1 CR0 BR1 DR1 AR1 EL0 DL0 BL1 DL1,NG 0 2)::
(makeTM BR1 HR1 CR0 CL0 DR0 EL1 AL1 AR1 CR1 EL0,NG 0 2)::
(makeTM BR1 HR1 CR0 CL0 DR1 AR1 EL0 DL0 BL1 DL1,NG 0 2)::
(makeTM BR1 HR1 CR0 CR1 DL0 BR0 EL0 DL1 BR1 EL1,NG 0 1)::
(makeTM BR1 HR1 CR0 DR0 DR1 AR1 DL1 EL0 BL1 AL0,NG 0 7)::
(makeTM BR1 HR1 CR0 DL1 CL1 BR0 EL0 AL0 AR0 EL0,NG 0 2)::
(makeTM BR1 HR1 CR0 EL1 CL1 DL0 AR1 BL0 ER0 DR1,NG 0 3)::
(makeTM BR1 HR1 CR0 EL1 DR1 AR0 BL1 DL0 DL1 ER1,NG 0 5)::
(makeTM BR1 HR1 CR0 ER1 DR0 AR1 DL0 BL1 DL1 ER0,NG 0 5)::
(makeTM BR1 HR1 CR0 ER1 DL1 CR1 CL0 BL1 AR1 EL0,NG 0 2)::
(makeTM BR1 HR1 CR0 ER1 DL1 CR1 DL1 BL1 AR1 EL0,NG 0 2)::
(makeTM BR1 HR1 CR0 ER1 DL1 DR0 EL0 DL1 AR0 CL0,NG 0 4)::
(makeTM BR1 HR1 CL1 BR0 AL0 DL1 ER1 EL0 AR1 DL0,NG 0 4)::
(makeTM BR1 HR1 CL1 BR0 DL0 CL0 EL1 AR0 BR1 AL0,NG 0 3)::
(makeTM BR1 HR1 CL1 BR0 DL0 DL1 EL0 AR1 AR0 BL1,NG 0 4)::
(makeTM BR1 HR1 CL1 BR0 EL0 DL0 AR1 CL1 ER1 DL1,NG 0 3)::
(makeTM BR1 HR1 CL1 BR1 DR0 CL0 BL0 ER1 ER0 AL1,NG 0 2)::
(makeTM BR1 HR1 CL1 BR1 DL1 DL0 BR0 ER0 CL0 ER1,NG 0 1)::
(makeTM BR1 HR1 CL1 BR1 EL1 DR0 AL1 CR1 DL1 BL0,NG 0 5)::
(makeTM BR1 HR1 CL1 DR0 DL0 BL1 AR0 ER0 CL0 ER1,NG 0 3)::
(makeTM BR1 HR1 CL1 DR1 AR0 CL0 ER0 BR1 EL0 BL1,NG 0 3)::
(makeTM BR1 HR1 CL1 EL0 CR1 DL0 BL1 AR1 ER1 AR0,NG 0 3)::
(makeTM BR1 HR1 CL1 EL0 DL0 BL0 ER1 BL0 ER1 AR0,NG 0 4)::
(makeTM BR1 HR1 CL1 EL0 DL1 BL0 BR0 DL0 ER1 AR0,NG 0 4)::
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 BL1 ER0 DR0 AR1,NG 0 6)::
(makeTM BR1 HR1 CL1 ER0 DL0 BL0 DR1 AR0 CL0 BR1,NG 0 4)::
(makeTM BR1 HR1 CL1 EL1 DR1 DL0 BL0 ER0 CR1 AL0,NG 0 7)::
(makeTM BR1 HR1 CL1 ER1 AL1 DL0 CR0 BL1 AL0 ER0,NG 0 12)::
(makeTM BR1 HR1 CL1 ER1 AL1 DL0 DR1 BL1 AL0 ER0,NG 0 12)::
(makeTM BR1 HR1 CL1 ER1 AL1 DL1 BR1 BL0 DL1 ER0,NG 0 11)::
(makeTM BR1 HR1 CL1 ER1 AL1 DL1 ER0 BL0 CL1 CR0,NG 0 11)::
(makeTM BR1 HR1 CL1 ER1 AL1 DL1 ER0 BL0 DL1 CR0,NG 0 11)::
(makeTM BR1 HR1 CL1 ER1 DL0 BL0 DR1 AR0 EL0 DL0,NG 0 4)::
(makeTM BR1 HR1 CR1 AR1 CL0 DL0 EL1 BR0 BR0 DL0,NG 0 2)::
(makeTM BR1 HR1 CR1 AR1 DL0 CR1 BR0 EL0 DL1 BR0,NG 0 2)::
(makeTM BR1 HR1 CR1 AR1 DL0 EL0 BR0 EL0 DL1 BR0,NG 0 2)::
(makeTM BR1 HR1 CR1 BR0 DL0 CL1 EL0 BL1 ER0 AL1,NG 0 4)::
(makeTM BR1 HR1 CR1 BR0 DR0 DL0 EL1 AR1 CL1 EL0,NG 0 5)::
(makeTM BR1 HR1 CR1 BR0 DL1 CR1 ER1 EL0 CL0 AR0,NG 0 2)::
(makeTM BR1 HR1 CR1 BL1 DL0 ER0 AL1 CL0 BR0 CR0,NG 0 4)::
(makeTM BR1 HR1 CR1 BL1 DL0 ER0 AL1 DL0 AR1 CR0,NG 0 5)::
(makeTM BR1 HR1 CR1 BL1 DL0 ER0 AL1 DL0 CR1 CR0,NG 0 4)::
(makeTM BR1 HR1 CR1 BL1 DR0 DR1 EL0 CR0 BL0 EL1,NG 0 1)::
(makeTM BR1 HR1 CR1 BL1 DR0 ER0 DL1 EL0 AR0 BL0,NG 0 3)::
(makeTM BR1 HR1 CR1 BL1 DL1 DR0 AL1 ER1 EL0 CL1,NG 0 4)::
(makeTM BR1 HR1 CR1 BL1 DR1 DR0 EL0 CR0 AL1 EL0,NG 0 5)::
(makeTM BR1 HR1 CR1 BR1 DL1 BR0 AL1 EL0 DL0 BL1,NG 0 3)::
(makeTM BR1 HR1 CR1 DR0 DL0 AR0 EL0 CR0 BL1 DL1,NG 0 2)::
(makeTM BR1 HR1 CR1 DL1 DL0 ER0 BL0 BL1 CR0 ER1,NG 0 1)::
(makeTM BR1 HR1 CR1 DR1 CL1 BL0 EL0 AR0 ER1 DL0,NG 0 6)::
(makeTM BR1 HR1 CR1 EL0 DL0 AR1 AR0 BL1 BL0 CR0,NG 0 2)::
(makeTM BR1 HR1 CR1 EL0 DL0 AR1 BL0 BL1 CR0 AR0,NG 0 2)::
(makeTM BR1 HR1 CR1 EL0 DL0 AR1 BL1 CR0 BL0 AR0,NG 0 2)::
(makeTM BR1 HR1 CR1 EL0 DR1 AR0 BL1 BL1 DL0 ER0,NG 0 5)::
(makeTM BR1 HR1 CR1 EL0 DR1 AR0 BL1 BL1 DL0 ER1,NG 0 5)::
(makeTM BR1 HR1 CR1 EL0 DR1 AR0 BL1 ER0 DL0 BL1,NG 0 5)::
(makeTM BR1 HR1 CR1 EL0 DR1 AR0 BL1 ER0 DL0 ER0,NG 0 5)::
(makeTM BR1 HR1 CR1 EL0 DR1 AR0 BL1 ER0 DL0 ER1,NG 0 5)::
(makeTM BR1 HR1 CR1 EL0 DR1 DL0 BL1 AR0 BL0 CL1,NG 0 5)::
(makeTM BR1 HR1 CR1 EL1 DR1 CR0 EL0 DR0 BL1 BL0,NG 0 1)::
(makeTM BR1 HR1 CR1 ER1 CL1 DL0 DR1 EL0 DL0 AR0,NG 0 6)::
(makeTM BR1 HR1 CR1 ER1 DL0 CR0 BL0 BL1 DL1 ER0,NG 0 1)::
(makeTM BR1 HR1 CR1 ER1 DL1 EL0 AL1 CL0 BR0 DR0,NG 0 3)::
(makeTM BR1 AL0 CL0 BR0 AR1 DL1 AL1 ER0 HR1 DR1,NG 0 2)::
(makeTM BR1 AL0 CL0 DR0 CL0 AL1 ER0 HR1 EL1 CR1,NG 0 2)::
(makeTM BR1 AL0 CL0 ER0 AR1 DL0 AL1 DR1 BR0 HR1,NG 0 2)::
(makeTM BR1 AL0 CR0 HR1 BL1 DR1 ER1 DL0 AL1 BR0,NG 0 4)::
(makeTM BR1 AL0 CR0 HR1 DL0 ER1 AL1 ER0 DR1 EL1,NG 0 2)::
(makeTM BR1 AL0 CR0 HR1 DL1 CL0 AL1 ER1 DR1 ER0,NG 0 2)::
(makeTM BR1 AL0 CR0 HR1 DL1 DR1 AL1 ER1 DR1 ER0,NG 0 2)::
(makeTM BR1 AL0 CR0 HR1 DR1 BL0 ER1 DL0 AL1 BR0,NG 0 4)::
(makeTM BR1 AL0 CR0 HR1 DR1 BR1 ER1 DL0 AL1 BR0,NG 0 4)::
(makeTM BR1 AL0 CR0 HR1 DR1 CR0 ER1 DL0 AL1 BR0,NG 0 4)::
(makeTM BR1 AL0 CR0 HR1 DR1 DR1 ER1 DL0 AL1 BR0,NG 0 4)::
(makeTM BR1 AL0 CR0 AR0 DR1 DL0 AL1 ER1 BR0 HR1,NG 0 3)::
(makeTM BR1 AL0 CR0 AL1 CL0 DR1 BL1 ER0 BR0 HR1,NG 0 3)::
(makeTM BR1 AL0 CR0 AL1 CL1 DR1 HR1 ER1 BR0 BL1,NG 0 3)::
(makeTM BR1 AL0 CR0 BR0 DR1 DL0 AL1 ER1 BR0 HR1,NG 0 3)::
(makeTM BR1 AL0 CR0 BR0 DR1 EL0 AL1 ER0 AL1 HR1,NG 0 3)::
(makeTM BR1 AL0 CR0 BR1 CL1 DR1 HR1 ER0 AL1 EL1,NG 0 3)::
(makeTM BR1 AL0 CR0 CR0 DL1 ER1 CL0 HR1 AL1 BR1,NG 0 2)::
(makeTM BR1 AL0 CR0 CR1 DR0 EL0 BL1 AR1 AL1 HR1,NG 0 2)::
(makeTM BR1 AL0 CR0 CR1 DR0 EL1 EL0 AR1 AL1 HR1,NG 0 4)::
(makeTM BR1 AL0 CR0 CR1 DL1 BR1 EL0 CL1 HR1 AL1,NG 0 2)::
(makeTM BR1 AL0 CR0 DL0 DR1 DL0 AL1 ER1 BR0 HR1,NG 0 3)::
(makeTM BR1 AL0 CR0 DL0 DR1 EL1 AL1 ER1 BR0 HR1,NG 0 3)::
(makeTM BR1 AL0 CR0 DR0 AL1 BR1 EL1 CR1 DL0 HR1,NG 0 2)::
(makeTM BR1 AL0 CR0 DR0 AL1 ER1 CL1 BR1 HR1 AR1,NG 0 5)::
(makeTM BR1 AL0 CR0 DL1 AL1 ER1 AR1 CL1 HR1 DR0,NG 0 4)::
(makeTM BR1 AL0 CR0 DR1 AL1 HR1 EL1 ER0 CL1 DR0,NG 0 3)::
(makeTM BR1 AL0 CR0 EL0 DR1 DL0 AL1 ER1 BR0 HR1,NG 0 7)::
(makeTM BR1 AL0 CR0 ER0 CL1 DR1 BR1 AL1 HR1 BL1,NG 0 3)::
(makeTM BR1 AL0 CR0 ER0 CL1 DR1 BR1 AL1 HR1 DR1,NG 0 3)::
(makeTM BR1 AL0 CR0 ER0 DR1 DL0 AL1 AR1 AR0 HR1,NG 0 3)::
(makeTM BR1 AL0 CR0 EL1 CL1 DR1 HR1 ER0 AR1 AL1,NG 0 4)::
(makeTM BR1 AL0 CR0 EL1 DR1 CL1 BL1 BR0 AL0 HR1,NG 0 2)::
(makeTM BR1 AL0 CR0 EL1 DR1 EL0 BL1 BR0 AL0 HR1,NG 0 2)::
(makeTM BR1 AL0 CR0 ER1 CL1 DR0 HR1 AL1 BR0 DL1,NG 0 3)::
(makeTM BR1 AL0 CR0 ER1 CL1 DR1 BR1 AL1 HR1 AR0,NG 0 3)::
(makeTM BR1 AL0 CL1 HR1 AL1 DR1 CR1 ER0 CL1 CR1,NG 0 2)::
(makeTM BR1 AL0 CL1 HR1 ER1 DL1 ER1 AL0 BR1 CR0,NG 0 11)::
(makeTM BR1 AL0 CL1 AR0 ER1 DL0 AL1 CR1 HR1 BR0,NG 0 2)::
(makeTM BR1 AL0 CL1 BR0 DL1 AL1 EL0 HR1 AR1 EL0,NG 0 3)::
(makeTM BR1 AL0 CL1 BR0 DL1 CR1 AL0 EL1 HR1 BR1,NG 0 2)::
(makeTM BR1 AL0 CL1 BR0 EL1 DR1 BL1 DR1 AL0 HR1,NG 0 2)::
(makeTM BR1 AL0 CL1 CR0 DR0 DR1 AR1 EL1 HR1 AL1,NG 0 12)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER0 BL1 AL0 HR1,NG 0 11)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER0 BR1 AL0 HR1,NG 0 11)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER0 CR0 AL0 HR1,NG 0 11)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER1 BL1 CL1 HR1,NG 0 11)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER1 BR1 CL1 HR1,NG 0 11)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER1 BR1 DL0 HR1,NG 0 11)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER1 CR0 CL1 HR1,NG 0 11)::
(makeTM BR1 AL0 CL1 CR1 HR1 DL1 AL1 ER0 AR0 ER1,NG 0 3)::
(makeTM BR1 AL0 CL1 CR1 EL1 DR1 CR1 BR0 HR1 AL0,NG 0 2)::
(makeTM BR1 AL0 CL1 DR0 HR1 AL1 ER0 ER1 AR1 CL1,NG 0 12)::
(makeTM BR1 AL0 CL1 DR0 CL1 AL1 HR1 ER1 CR0 ER1,NG 0 3)::
(makeTM BR1 AL0 CL1 DR0 DR1 CL0 ER0 HR1 AR1 AR1,NG 0 4)::
(makeTM BR1 AL0 CL1 DR0 DR1 CL0 ER0 HR1 AR1 DL0,NG 0 4)::
(makeTM BR1 AL0 CL1 DR0 DR1 CL0 ER0 HR1 AR1 DR1,NG 0 4)::
(makeTM BR1 AL0 CL1 DR0 DR1 CL0 ER0 HR1 AR1 ER0,NG 0 4)::
(makeTM BR1 AL0 CL1 DR0 DR1 CL0 ER0 HR1 DL1 AR1,NG 0 4)::
(makeTM BR1 AL0 CL1 DR0 EL1 AL1 HR1 ER1 BR0 CL1,NG 0 3)::
(makeTM BR1 AL0 CL1 DR1 HR1 AL1 ER0 DR0 EL1 CR1,NG 0 3)::
(makeTM BR1 AL0 CL1 DR1 EL0 AL1 BL1 DR0 AR1 HR1,NG 0 5)::
(makeTM BR1 AL0 CL1 EL0 AL1 DR1 CR1 BR0 DR0 HR1,NG 0 2)::
(makeTM BR1 AL0 CL1 ER0 DL1 BL1 AL1 DR1 HR1 CR1,NG 0 2)::
(makeTM BR1 AL0 CL1 ER0 DL1 CR0 EL1 HR1 BR0 AL1,NG 0 2)::
(makeTM BR1 AL0 CL1 ER1 AL1 DR1 BL1 DR0 HR1 AR1,NG 0 3)::
(makeTM BR1 AL0 CL1 ER1 AL1 DR1 BL1 DR0 HR1 CR1,NG 0 2)::
(makeTM BR1 AL0 CR1 HR1 DL0 ER1 AR1 CL0 DL1 ER0,NG 0 2)::
(makeTM BR1 AL0 CR1 HR1 DR0 CR0 DL1 ER1 HR1 AL1,NG 0 3)::
(makeTM BR1 AL0 CR1 HR1 DR0 CL1 ER1 ER0 AL1 ER1,NG 0 5)::
(makeTM BR1 AL0 CR1 HR1 DR0 CR1 EL1 DL0 AL1 CR0,NG 0 2)::
(makeTM BR1 AL0 CR1 HR1 DR0 DL1 ER1 AR0 CL1 EL0,NG 0 5)::
(makeTM BR1 AL0 CR1 HR1 DR0 EL0 DL1 ER1 AL1 CR0,NG 0 2)::
(makeTM BR1 AL0 CR1 HR1 DL1 DR1 AL1 ER1 EL1 CR0,NG 0 2)::
(makeTM BR1 AL0 CR1 AL0 DR0 CR0 DL1 ER1 HR1 BL1,NG 0 3)::
(makeTM BR1 AL0 CR1 AR0 DL0 ER1 HR1 CL1 BR0 AL1,NG 0 4)::
(makeTM BR1 AL0 CR1 AL1 BL1 DR1 HR1 ER0 CL1 ER0,NG 0 3)::
(makeTM BR1 AL0 CR1 AL1 BL1 DR1 EL1 DR0 BL1 HR1,NG 0 3)::
(makeTM BR1 AL0 CR1 AL1 CL1 DR0 HR1 ER1 BL1 BR0,NG 0 4)::
(makeTM BR1 AL0 CR1 AL1 DR0 CR0 DL1 ER0 HR1 AL1,NG 0 3)::
(makeTM BR1 AL0 CR1 BL0 DL1 CR0 EL1 BL1 AL0 HR1,NG 0 3)::
(makeTM BR1 AL0 CR1 BL1 DR0 ER1 AL1 DR0 HR1 AL1,NG 0 2)::
(makeTM BR1 AL0 CR1 CL1 DL1 ER0 AL0 BR0 HR1 DR0,NG 0 3)::
(makeTM BR1 AL0 CR1 CR1 DL1 DR1 AR0 EL0 HR1 CL1,NG 0 3)::
(makeTM BR1 AL0 CR1 DR0 DL1 ER0 BR1 AL1 HR1 AR1,NG 0 4)::
(makeTM BR1 AL0 CR1 DL1 BL1 ER1 HR1 AL0 CL1 ER0,NG 0 3)::
(makeTM BR1 AL0 CR1 DR1 DL0 ER0 AR1 AL1 BR0 HR1,NG 0 2)::
(makeTM BR1 AL0 CR1 DR1 DL0 ER1 AL1 BL0 BR0 HR1,NG 0 9)::
(makeTM BR1 AL0 CR1 DR1 DR1 HR1 EL1 DR0 CL0 AL1,NG 0 3)::
(makeTM BR1 AL0 CR1 ER0 DL1 AR0 BL1 DL1 HR1 DL0,NG 0 5)::
(makeTM BR1 AL0 CR1 EL1 DR1 HR1 EL1 DR0 BL0 AL1,NG 0 5)::
(makeTM BR1 AL0 CR1 EL1 DR1 AL1 BL1 DR0 HR1 CL1,NG 0 2)::
(makeTM BR1 AL0 CR1 ER1 DL0 DR0 BR0 AL1 AR1 HR1,NG 0 2)::
(makeTM BR1 AL0 CR1 ER1 DR0 HR1 EL1 DL0 AL1 ER0,NG 0 3)::
(makeTM BR1 AL0 CR1 ER1 DR0 HR1 EL1 DR0 AL1 ER0,NG 0 3)::
(makeTM BR1 AR0 CL0 AR0 DL1 CR1 EL0 BL1 AR0 HR1,NG 0 12)::
(makeTM BR1 AR0 CL0 AR1 HR1 DL1 EL0 ER1 AL1 CL1,NG 0 11)::
(makeTM BR1 AR0 CL0 AR1 DL0 CL1 EL1 BR1 BR1 HR1,NG 0 11)::
(makeTM BR1 AR0 CL0 AR1 EL1 DL1 CL0 DL1 BR1 HR1,NG 0 11)::
(makeTM BR1 AR0 CL0 BL1 DL0 AL1 DR0 EL1 AR1 HR1,NG 0 4)::
(makeTM BR1 AR0 CL0 CR1 AL1 DL0 EL1 DR0 BL1 HR1,NG 0 5)::
(makeTM BR1 AR0 CL0 DL0 DR0 BL1 AR1 EL1 CL1 HR1,NG 0 2)::
(makeTM BR1 AR0 CL0 DL1 ER1 DL1 BL1 AR1 CR1 HR1,NG 0 2)::
(makeTM BR1 AR0 CL0 EL0 DL0 BL1 ER1 HR1 AR1 EL1,NG 0 4)::
(makeTM BR1 AR0 CL0 EL0 DL1 CR1 AR1 BL1 HR1 CR0,NG 0 12)::
(makeTM BR1 AR0 CL0 ER1 AL1 DL0 BL1 HR1 AR1 EL1,NG 0 5)::
(makeTM BR1 AR0 CL0 ER1 AR1 DL1 BL1 AR1 HR1 CL1,NG 0 3)::
(makeTM BR1 AR0 CL0 ER1 CR1 DL1 BL1 AR1 HR1 CL1,NG 0 3)::
(makeTM BR1 AR0 CL0 ER1 DL1 CR1 AR1 BL1 HR1 AL1,NG 0 3)::
(makeTM BR1 AR0 CR0 HR1 DR0 AL0 DL1 EL0 ER1 CL0,NG 0 2)::
(makeTM BR1 AR0 CR0 AR0 DR1 HR1 EL0 EL1 AR1 DL1,NG 0 3)::
(makeTM BR1 AR0 CR0 AR1 DL0 HR1 EL0 DL1 AL1 CR1,NG 0 3)::
(makeTM BR1 AR0 CR0 AR1 DL0 HR1 EL0 DL1 AL1 DL1,NG 0 3)::
(makeTM BR1 AR0 CL1 HR1 DL1 CR1 AR0 EL0 CL1 DL0,NG 0 4)::
(makeTM BR1 AR0 CL1 AR1 HR1 DL1 EL0 ER1 AL1 CL1,NG 0 11)::
(makeTM BR1 AR0 CL1 AR1 DL0 DR1 AL1 EL1 HR1 CL1,NG 0 11)::
(makeTM BR1 AR0 CL1 CL0 DR1 BL1 ER0 ER1 HR1 AR1,NG 0 2)::
(makeTM BR1 AR0 CL1 DL0 ER1 DR1 AL1 BL1 HR1 CR1,NG 0 2)::
(makeTM BR1 AR0 CL1 EL0 HR1 DL0 AR1 BL1 DR1 EL1,NG 0 2)::
(makeTM BR1 AR0 CL1 ER0 AR1 DL1 BL0 HR1 AL0 AR0,NG 0 12)::
(makeTM BR1 AR0 CL1 ER0 ER1 DL1 BL0 HR1 AL0 AR0,NG 0 12)::
(makeTM BR1 AR0 CL1 ER1 AR1 DL1 BL0 HR1 CL1 AL1,NG 0 12)::
(makeTM BR1 AR0 CR1 AR1 DL0 HR1 EL0 DL1 AL1 CR1,NG 0 3)::
(makeTM BR1 AR0 CR1 AR1 DL0 DR1 AL1 EL1 HR1 CL1,NG 0 11)::
(makeTM BR1 AR0 CR1 AR1 DL0 ER1 AL1 CL1 HR1 DL1,NG 0 3)::
(makeTM BR1 AR0 CR1 BL0 DL1 CR0 EL1 BL1 AL0 HR1,NG 0 3)::
(makeTM BR1 AL1 AL0 CR1 DL0 BR0 HR1 EL1 CL1 ER1,NG 0 3)::
(makeTM BR1 AL1 CL0 BR0 AR0 DL1 EL0 HR1 CL1 ER1,NG 0 12)::
(makeTM BR1 AL1 CL0 DR0 HR1 DL1 ER0 AL0 CL1 ER1,NG 0 3)::
(makeTM BR1 AL1 CL0 DR0 AL1 BL1 ER0 BR0 HR1 BL1,NG 0 4)::
(makeTM BR1 AL1 CL0 DR0 AL1 BL1 ER0 BR0 HR1 BR1,NG 0 4)::
(makeTM BR1 AL1 CL0 DR0 AL1 BL1 ER0 DR0 HR1 BL1,NG 0 4)::
(makeTM BR1 AL1 CL0 DR0 AL1 BL1 ER0 DR0 HR1 BR1,NG 0 4)::
(makeTM BR1 AL1 CL0 ER0 HR1 DL1 ER1 AL0 BL1 AR1,NG 0 2)::
(makeTM BR1 AL1 CL0 ER0 DL1 CL0 AR1 HR1 AR1 BR0,NG 0 4)::
(makeTM BR1 AL1 CR0 BR0 DL0 AL0 EL1 HR1 BR0 CL1,NG 0 5)::
(makeTM BR1 AL1 CR0 BR0 DL0 AL0 EL1 HR1 BR1 CL1,NG 0 5)::
(makeTM BR1 AL1 CR0 CL1 DR1 CL0 ER1 HR1 AL1 ER0,NG 0 3)::
(makeTM BR1 AL1 CR0 DR0 CL1 DL0 ER0 AL0 AR1 HR1,NG 0 3)::
(makeTM BR1 AL1 CR0 DL1 CL1 BR0 AL0 EL0 AL0 HR1,NG 0 5)::
(makeTM BR1 AL1 CR0 DR1 CL1 AL0 ER1 EL0 HR1 BR0,NG 0 8)::
(makeTM BR1 AL1 CR0 EL1 DL1 BR0 CL1 HR1 AL0 EL0,NG 0 5)::
(makeTM BR1 AL1 CR0 ER1 CL1 DL0 AL1 HR1 AL0 BR0,NG 0 4)::
(makeTM BR1 AL1 CR0 ER1 DL0 HR1 EL1 DL0 AR0 DL0,NG 0 12)::
(makeTM BR1 AL1 CR0 ER1 DL1 CR0 AR1 DL0 HR1 DL1,NG 0 2)::
(makeTM BR1 AL1 CL1 AR0 DR1 CL0 ER0 HR1 BL0 AR1,NG 0 2)::
(makeTM BR1 AL1 CL1 BR0 ER0 DL0 CL0 HR1 BL1 AR0,NG 0 2)::
(makeTM BR1 AL1 CL1 CR0 AR0 DL1 EL0 HR1 CR1 EL0,NG 0 2)::
(makeTM BR1 AL1 CL1 CR0 EL1 DR1 DL0 BL1 AL1 HR1,NG 0 4)::
(makeTM BR1 AL1 CL1 CR1 DL1 BR0 HR1 EL1 AL0 BR1,NG 0 2)::
(makeTM BR1 AL1 CL1 DR0 AL1 BL0 ER0 DR0 HR1 AL0,NG 0 4)::
(makeTM BR1 AL1 CL1 DR0 AL1 BL0 ER1 DR0 HR1 CL1,NG 0 4)::
(makeTM BR1 AL1 CL1 DR0 EL1 BR0 BL0 AL0 AR1 HR1,NG 0 3)::
(makeTM BR1 AL1 CL1 DR1 DL1 CL0 AR0 ER0 HR1 AL0,NG 0 12)::
(makeTM BR1 AL1 CL1 DR1 DL1 CL0 AR0 EL1 HR1 CR1,NG 0 3)::
(makeTM BR1 AL1 CL1 DR1 EL0 DL1 BR1 BR0 HR1 AL0,NG 0 2)::
(makeTM BR1 AL1 CL1 ER0 AL0 DL1 BR1 HR1 BR0 EL0,NG 0 3)::
(makeTM BR1 AL1 CL1 ER0 DR1 CL0 ER0 HR1 BL1 AR1,NG 0 2)::
(makeTM BR1 AL1 CL1 ER1 DL0 CL0 ER1 BR1 AR0 HR1,NG 0 12)::
(makeTM BR1 AL1 CR1 BL0 DR1 HR1 ER0 AL1 CL1 ER0,NG 0 2)::
(makeTM BR1 AL1 CR1 BL0 DR1 HR1 EL1 DR0 AL1 DR1,NG 0 2)::
(makeTM BR1 AL1 CR1 BL0 DR1 HR1 EL1 DR0 AR1 DR1,NG 0 2)::
(makeTM BR1 AL1 CR1 BL0 DR1 HR1 ER1 DR0 AL0 DR0,NG 0 2)::
(makeTM BR1 AL1 CR1 BL0 DR1 AL1 ER0 HR1 BL1 ER0,NG 0 3)::
(makeTM BR1 AL1 CR1 CL0 AL0 DR1 ER0 HR1 BL1 ER1,NG 0 4)::
(makeTM BR1 AL1 CR1 CL0 DL1 DR1 EL1 CR0 HR1 AL0,NG 0 2)::
(makeTM BR1 AL1 CR1 CR0 AL0 DL0 EL1 BR0 HR1 AL0,NG 0 2)::
(makeTM BR1 AL1 CR1 CR0 DR0 EL0 EL0 BR0 AL0 HR1,NG 0 3)::
(makeTM BR1 AL1 CR1 CR1 DL1 DR1 AR0 EL0 HR1 CL1,NG 0 3)::
(makeTM BR1 AL1 CR1 DL1 DR1 CR0 EL1 AL0 HR1 BL0,NG 0 3)::
(makeTM BR1 AL1 CR1 ER0 DR0 HR1 EL0 BR0 AL0 CL0,NG 0 3)::
(makeTM BR1 AL1 CR1 ER0 DR0 HR1 EL0 BR0 AL0 EL0,NG 0 3)::
(makeTM BR1 AL1 CR1 EL1 DR0 HR1 ER0 DR1 AL1 BL0,NG 0 2)::
(makeTM BR1 AL1 CR1 EL1 DL1 DR1 EL1 CR0 HR1 AL0,NG 0 2)::
(makeTM BR1 AR1 CL0 DL0 DL1 BR0 AR0 CL1 HR1 HR1,NG 0 1)::
(makeTM BR1 AR1 CL1 BR0 DL0 CL1 AR1 EL1 HR1 AL0,NG 0 3)::
(makeTM BR1 AR1 CL1 BR0 DL0 CL1 DR1 EL1 HR1 AL0,NG 0 3)::
(makeTM BR1 AR1 CL1 CR0 EL1 DL0 CL0 DL1 AR0 HR1,NG 0 3)::
(makeTM BR1 AR1 CL1 EL0 AR1 DL0 BL1 DR0 HR1 AR0,NG 0 5)::
(makeTM BR1 AR1 CL1 ER0 DR0 CL0 ER1 HR1 BL1 AL1,NG 0 2)::
(makeTM BR1 AR1 CL1 EL1 DR0 CL0 BL1 DR1 HR1 AR0,NG 0 2)::
(makeTM BR1 AR1 CR1 ER0 DL0 BL1 AL0 DL1 HR1 CR0,NG 0 3)::
(makeTM BR1 BL0 BL1 CR1 HR1 DR1 EL1 DR0 AR0 EL0,NG 0 2)::
(makeTM BR1 BL0 CL0 DR1 AL1 CR1 ER0 HR1 BL1 ER0,NG 0 2)::
(makeTM BR1 BL0 CL0 DR1 AL1 DR0 ER0 HR1 BL1 AL0,NG 0 2)::
(makeTM BR1 BL0 CL0 DR1 AL1 DR0 ER0 HR1 BL1 ER0,NG 0 2)::
(makeTM BR1 BL0 CL0 DR1 AL1 DR0 ER1 HR1 EL1 CL0,NG 0 2)::
(makeTM BR1 BL0 CR0 AR0 DL0 AR1 EL0 HR1 CR1 EL1,NG 0 2)::
(makeTM BR1 BL0 CR0 BL0 DR1 ER0 EL1 HR1 AL0 EL1,NG 0 12)::
(makeTM BR1 BL0 CR0 BR1 DL0 AR0 EL1 HR1 AL0 CL1,NG 0 4)::
(makeTM BR1 BL0 CR0 ER1 DR1 ER0 BL1 HR1 AL0 EL1,NG 0 12)::
(makeTM BR1 BL0 CR0 ER1 DR1 ER0 EL1 HR1 AL0 EL1,NG 0 12)::
(makeTM BR1 BL0 CL1 AR1 HR1 DL1 EL0 ER1 AL1 DR0,NG 0 5)::
(makeTM BR1 BL0 CL1 BR1 HR1 DL1 AL1 ER1 AL1 DR0,NG 0 11)::
(makeTM BR1 BL0 CL1 DR0 AR1 DL0 AL1 ER1 CR0 HR1,NG 0 3)::
(makeTM BR1 BL0 CL1 DR1 DR0 BL1 EL1 AR0 HR1 CL0,NG 0 2)::
(makeTM BR1 BL0 CL1 DR1 EL0 AL1 AL1 DR0 DR0 HR1,NG 0 11)::
(makeTM BR1 BL0 CL1 DR1 EL1 AL1 AL1 DR0 BR1 HR1,NG 0 11)::
(makeTM BR1 BL0 CL1 DR1 EL1 AL1 AL1 DR0 CR0 HR1,NG 0 11)::
(makeTM BR1 BL0 CL1 EL0 HR1 DL1 AR1 DL0 ER1 AR0,NG 0 2)::
(makeTM BR1 BL0 CL1 ER0 AR1 DL0 CL0 AL1 CR1 HR1,NG 0 5)::
(makeTM BR1 BL0 CR1 AL0 DR1 HR1 EL1 DR0 CL0 AL1,NG 0 3)::
(makeTM BR1 BL0 CR1 ER0 DL0 HR1 AL1 DL1 BR0 ER1,NG 0 3)::
(makeTM BR1 BL0 CR1 ER1 DL1 HR1 BR1 AL1 AL0 DR0,NG 0 11)::
(makeTM BR1 BR0 CL0 AR1 DL1 CL1 ER1 BL1 HR1 DR1,NG 0 3)::
(makeTM BR1 BR0 CR0 DL0 DL0 AR0 EL0 HR1 AR1 EL1,NG 0 3)::
(makeTM BR1 BR0 CR0 DL1 DL0 CR0 EL0 HR1 AR1 EL1,NG 0 2)::
(makeTM BR1 BR0 CL1 AR1 DL0 AL1 HR1 EL0 BR1 EL1,NG 0 2)::
(makeTM BR1 BR0 CR1 EL1 DR0 HR1 ER0 DR1 AL1 BL0,NG 0 2)::
(makeTM BR1 BL1 CL0 DR0 AL1 BL1 ER1 CR1 HR1 AR1,NG 0 5)::
(makeTM BR1 BL1 CL0 ER0 AR0 DL1 ER1 CL1 HR1 AR1,NG 0 3)::
(makeTM BR1 BL1 CL0 ER0 DL1 CR0 AL1 AL1 HR1 AR1,NG 0 3)::
(makeTM BR1 BL1 CL0 ER0 DL1 CR1 AL1 AL1 HR1 AR1,NG 0 3)::
(makeTM BR1 BL1 CL1 BR0 EL0 DL0 BL0 HR1 AL1 AR0,NG 0 3)::
(makeTM BR1 BL1 CL1 DR0 AL1 CL0 AR0 ER0 HR1 AR0,NG 0 4)::
(makeTM BR1 BL1 CL1 DR0 AL1 CL0 AR0 ER1 HR1 BL0,NG 0 4)::
(makeTM BR1 BL1 CL1 DR1 HR1 DL0 AR1 EL0 BR0 EL1,NG 0 3)::
(makeTM BR1 BL1 CL1 ER0 AL1 DR1 DL0 EL0 HR1 CR1,NG 0 2)::
(makeTM BR1 BL1 CL1 ER0 DL0 AR0 AR1 DL0 HR1 CR0,NG 0 3)::
(makeTM BR1 BL1 CR1 AL0 DR0 CR0 EL0 ER0 AL1 HR1,NG 0 4)::
(makeTM BR1 BL1 CR1 BL0 DR0 AL1 BL1 ER1 HR1 AR0,NG 0 4)::
(makeTM BR1 BL1 CR1 BL0 DR1 HR1 ER0 DR0 EL1 AR1,NG 0 3)::
(makeTM BR1 BL1 CR1 EL0 DL1 BR1 HR1 AL0 CR0 EL1,NG 0 4)::
(makeTM BR1 BL1 CR1 ER1 DL0 AR1 AL0 DL1 HR1 CR0,NG 0 3)::
(makeTM BR1 BR1 CL1 ER0 AL1 DL0 BL1 HR1 AR0 EL0,NG 0 5)::
(makeTM BR1 BR1 CL1 ER0 AL1 DL0 BL1 HR1 AR0 EL1,NG 0 5)::
(makeTM BR1 CL0 AL0 ER0 DR1 BR1 EL1 HR1 CR1 AL1,NG 0 11)::
(makeTM BR1 CL0 AL1 CR0 DL1 EL1 ER1 HR1 ER0 AR1,NG 0 3)::
(makeTM BR1 CL0 BL1 CR1 AL1 DL1 ER1 BR0 HR1 DR1,NG 0 6)::
(makeTM BR1 CL0 CL0 AR0 EL1 DL1 CL1 HR1 BR0 AR0,NG 0 2)::
(makeTM BR1 CL0 CL0 AR0 EL1 DL1 CL1 HR1 BR0 EL1,NG 0 2)::
(makeTM BR1 CL0 CR0 AR1 DL0 EL0 AL1 HR1 BR0 EL1,NG 0 4)::
(makeTM BR1 CL0 CR0 ER1 DL1 EL1 AL1 HR1 BR0 AR1,NG 0 5)::
(makeTM BR1 CL0 CL1 AR0 DR0 BL1 AR1 ER1 HR1 AR1,NG 0 2)::
(makeTM BR1 CL0 CL1 BR0 DL0 CL1 AR1 EL1 HR1 AL0,NG 0 3)::
(makeTM BR1 CL0 CL1 DR1 AL1 BL1 HR1 ER1 AL0 ER0,NG 0 3)::
(makeTM BR1 CL0 CL1 ER1 DR0 DL0 AL1 DL0 AR0 HR1,NG 0 12)::
(makeTM BR1 CL0 CR1 AR0 DL1 CL1 ER0 AR1 HR1 DR0,NG 0 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DL0 CL0 ER0 AR0 HR1,NG 0 7)::
(makeTM BR1 CR0 CR0 HR1 DL1 ER1 AL0 EL1 DL0 AL1,NG 0 8)::
(makeTM BR1 CR0 CL1 HR1 AR1 DL1 AR1 EL0 BR1 EL0,NG 0 11)::
(makeTM BR1 CR0 CL1 HR1 AR1 DL1 ER0 DL0 AL0 CL1,NG 0 11)::
(makeTM BR1 CR0 CL1 HR1 AR1 DL1 ER1 DL0 CL1 CR0,NG 0 11)::
(makeTM BR1 CR0 CL1 HR1 DL0 CL1 ER1 EL0 AR0 CR1,NG 0 12)::
(makeTM BR1 CR0 CL1 HR1 DL0 CL1 ER1 EL0 AR0 EL0,NG 0 12)::
(makeTM BR1 CR0 CL1 AR1 EL0 DL0 CL1 DL1 AR0 HR1,NG 0 3)::
(makeTM BR1 CR0 CL1 BR0 DL0 CL1 AR1 EL1 HR1 AL0,NG 0 3)::
(makeTM BR1 CR0 CL1 BR0 DL1 AL1 AR0 EL1 CL0 HR1,NG 0 9)::
(makeTM BR1 CR0 CL1 CR0 HR1 DR1 AR1 EL0 AL1 EL1,NG 0 5)::
(makeTM BR1 CR0 CL1 DL0 AR1 BL0 EL0 BR0 HR1 CL0,NG 0 7)::
(makeTM BR1 CR0 CL1 DL1 AR1 BL0 EL0 AR1 HR1 CL0,NG 0 7)::
(makeTM BR1 CR0 CL1 DL1 AR1 BL0 EL1 AL1 HR1 CL0,NG 0 6)::
(makeTM BR1 CR0 CL1 DL1 AR1 BL0 EL1 AR1 HR1 CL0,NG 0 7)::
(makeTM BR1 CR0 CL1 ER0 AR1 DL1 AR1 DL0 HR1 DR1,NG 0 4)::
(makeTM BR1 CR0 CL1 EL1 DR1 BL0 HR1 AR1 AL0 ER0,NG 0 3)::
(makeTM BR1 CR0 CL1 ER1 DR1 DL1 AR1 DL0 HR1 AR0,NG 0 4)::
(makeTM BR1 CR0 CL1 ER1 DR1 DL1 AR1 DL0 HR1 CR0,NG 0 4)::
(makeTM BR1 CR0 CR1 AR0 DL0 DL0 AL1 EL1 HR1 DL1,NG 0 3)::
(makeTM BR1 CR0 CR1 BL0 DL1 AR1 EL0 BL1 HR1 CR1,NG 0 2)::
(makeTM BR1 CR0 CR1 BL0 DL1 AR1 EL1 BL1 HR1 BR0,NG 0 2)::
(makeTM BR1 CR0 CR1 BL0 DL1 AR1 EL1 BL1 HR1 BL1,NG 0 2)::
(makeTM BR1 CR0 CR1 BL1 DL0 AR0 EL1 DL0 BR1 HR1,NG 0 4)::
(makeTM BR1 CR0 CR1 BL1 DL1 AR1 EL1 AR1 HR1 DL0,NG 0 4)::
(makeTM BR1 CR0 CR1 BL1 DL1 AR1 EL1 CL0 HR1 CL0,NG 0 4)::
(makeTM BR1 CL1 AL0 BR0 BR1 DL1 ER0 AL1 HR1 DR1,NG 0 2)::
(makeTM BR1 CL1 AL0 BR0 DR0 DL1 ER0 AL1 HR1 CR1,NG 0 2)::
(makeTM BR1 CL1 AL0 BR0 DR0 DL1 ER0 AL1 HR1 DR1,NG 0 2)::
(makeTM BR1 CL1 AL0 BR0 DL1 DR1 ER0 AL1 HR1 DR0,NG 0 2)::
(makeTM BR1 CL1 AL0 BR0 DR1 CL0 AL1 DR0 HR1 HR1,NG 0 1)::
(makeTM BR1 CL1 AL1 DR1 AR1 CL0 HR1 ER0 BL1 ER0,NG 0 3)::
(makeTM BR1 CL1 AL1 DR1 AR1 CL0 EL1 DR0 AL1 HR1,NG 0 3)::
(makeTM BR1 CL1 AL1 ER0 DL0 BL1 AR0 BL1 HR1 DR1,NG 0 3)::
(makeTM BR1 CL1 CL0 AR1 ER1 DL0 AL1 AR0 HR1 BR0,NG 0 2)::
(makeTM BR1 CL1 CR0 AR1 DL0 DR0 AL1 EL0 BL1 HR1,NG 0 4)::
(makeTM BR1 CL1 CR0 DL1 DR1 HR1 BL0 ER1 AR0 EL0,NG 0 10)::
(makeTM BR1 CL1 CR0 DR1 DL1 ER1 AL1 DR0 HR1 AL0,NG 0 2)::
(makeTM BR1 CL1 CL1 BR0 DL0 DL0 ER1 AL1 DR0 HR1,NG 0 2)::
(makeTM BR1 CL1 CL1 ER0 HR1 DL0 AR1 EL1 AR1 CR1,NG 0 12)::
(makeTM BR1 CL1 CL1 ER1 DR0 CL0 BL0 AL1 AR0 HR1,NG 0 12)::
(makeTM BR1 CL1 CR1 BR0 DL0 ER1 AL1 DR1 HR1 BL1,NG 0 3)::
(makeTM BR1 CR1 AL0 HR1 DL1 DR0 AR1 EL1 CR1 EL0,NG 0 11)::
(makeTM BR1 CR1 AL1 CL0 EL1 DR0 CR0 BR0 BL0 HR1,NG 0 3)::
(makeTM BR1 CR1 AL1 DL0 DR0 BR0 EL1 CR0 BL0 HR1,NG 0 3)::
(makeTM BR1 CR1 CL0 HR1 DR1 CL1 EL1 DR0 AR1 EL0,NG 0 2)::
(makeTM BR1 CR1 CL1 BL0 DR1 AR0 EL1 AL1 HR1 DL1,NG 0 2)::
(makeTM BR1 CR1 CL1 EL0 DR1 DL0 BL1 AR1 HR1 AR0,NG 0 5)::
(makeTM BR1 CR1 CL1 ER0 DL0 BL1 AR1 DL1 HR1 CR1,NG 0 3)::
(makeTM BR1 CR1 CL1 ER1 DL0 BL0 AR1 DL1 AR0 HR1,NG 0 3)::
(makeTM BR1 CR1 CL1 ER1 DL1 CL0 BR1 AL1 DR0 HR1,NG 0 12)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 ER1 AL1 DL1 HR1,NG 0 1)::
(makeTM BR1 DL0 CL0 CR1 ER1 DL1 AL1 CR0 HR1 AR0,NG 0 4)::
(makeTM BR1 DL0 CR0 CR1 AL1 AR1 HR1 EL0 BR0 CL1,NG 0 3)::
(makeTM BR1 DL0 CR0 ER1 DL0 ER0 AL1 CL0 DR1 HR1,NG 0 2)::
(makeTM BR1 DL0 CL1 AR0 DR0 BL0 EL1 DR1 HR1 CL1,NG 0 2)::
(makeTM BR1 DL0 CL1 AR1 ER0 AL1 HR1 BL1 AL1 ER0,NG 0 3)::
(makeTM BR1 DL0 CL1 CR0 ER1 AR0 BL0 HR1 AL1 ER0,NG 0 2)::
(makeTM BR1 DL0 CL1 DR1 EL0 BR0 CR1 DL1 HR1 AL1,NG 0 2)::
(makeTM BR1 DL0 CL1 ER0 AL1 AR0 BL1 HR1 BR0 CR1,NG 0 5)::
(makeTM BR1 DL0 CL1 ER1 AL0 CR1 ER0 AL1 CR0 HR1,NG 0 2)::
(makeTM BR1 DL0 CR1 HR1 DL0 ER0 AL0 DL1 BR0 DR0,NG 0 5)::
(makeTM BR1 DL0 CR1 BL0 DR1 HR1 AL0 ER1 AL1 ER0,NG 0 2)::
(makeTM BR1 DL0 CR1 BR1 AL1 EL0 CL1 DR0 HR1 BR0,NG 0 5)::
(makeTM BR1 DL0 CR1 CL1 AL1 AR1 ER0 DL1 HR1 BR0,NG 0 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 AL1 CL0 DR0 AR1 HR1,NG 0 5)::
(makeTM BR1 DL0 CR1 ER0 AL1 AL1 CL0 DR1 AR1 HR1,NG 0 5)::
(makeTM BR1 DL0 CR1 ER0 AL1 DR0 CL0 AL1 AR1 HR1,NG 0 5)::
(makeTM BR1 DL0 CR1 ER0 AL1 DR0 CL0 DR0 AR1 HR1,NG 0 5)::
(makeTM BR1 DL0 CR1 ER0 AL1 DR0 CL0 DR1 AR1 HR1,NG 0 5)::
(makeTM BR1 DL0 CR1 ER0 DL0 ER0 BL1 DL1 HR1 AR1,NG 0 5)::
(makeTM BR1 DL0 CR1 ER1 AL0 BR1 HR1 CL1 AL1 ER0,NG 0 3)::
(makeTM BR1 DL0 CR1 ER1 AL0 DL0 ER0 AL1 CR0 HR1,NG 0 2)::
(makeTM BR1 DR0 CL0 AR0 ER1 DL1 BL1 AR1 CR1 HR1,NG 0 2)::
(makeTM BR1 DR0 CL0 AL1 DL0 CL1 ER1 BR0 AR1 HR1,NG 0 4)::
(makeTM BR1 DR0 CL0 BR0 AL1 CL1 HR1 ER1 AR1 CL0,NG 0 4)::
(makeTM BR1 DR0 CL0 BR0 AR1 CL1 EL1 BL1 DL0 HR1,NG 0 2)::
(makeTM BR1 DR0 CL0 DR0 AL1 CL1 HR1 ER1 AR1 CL0,NG 0 5)::
(makeTM BR1 DR0 CR0 HR1 DL0 AR0 EL0 BL0 AR1 EL1,NG 0 3)::
(makeTM BR1 DR0 CR0 HR1 DL0 AR0 EL0 DL0 AR1 EL1,NG 0 3)::
(makeTM BR1 DR0 CR0 AR0 DL1 AR0 DL1 EL0 AL1 HR1,NG 0 4)::
(makeTM BR1 DR0 CR0 EL1 DR1 EL0 BL1 BR0 AL0 HR1,NG 0 2)::
(makeTM BR1 DR0 CL1 HR1 AR0 DR1 EL0 DL1 CR1 CL0,NG 0 12)::
(makeTM BR1 DR0 CL1 AR1 DL0 AL1 EL1 BL0 BR0 HR1,NG 0 3)::
(makeTM BR1 DR0 CL1 BL0 AR0 AL1 ER1 DL0 CR1 HR1,NG 0 6)::
(makeTM BR1 DR0 CL1 BL1 ER0 DR1 AR1 BL0 HR1 CR0,NG 0 2)::
(makeTM BR1 DR0 CL1 BR1 BL0 DL0 ER0 CL0 AR1 HR1,NG 0 5)::
(makeTM BR1 DR0 CR1 HR1 DR1 CL1 EL0 AR0 BL1 EL0,NG 0 5)::
(makeTM BR1 DL1 CL0 AR1 AL1 BL1 EL1 DR0 AL0 HR1,NG 0 5)::
(makeTM BR1 DL1 CL0 BR0 AR1 CL1 AL1 ER0 HR1 DL0,NG 0 1)::
(makeTM BR1 DL1 CL0 BR0 BR1 AL1 ER0 CL1 HR1 DR1,NG 0 2)::
(makeTM BR1 DL1 CR0 AR0 DL0 HR1 ER1 DL0 AL1 AR0,NG 0 11)::
(makeTM BR1 DL1 CR0 DL0 AL1 BR0 CL1 ER0 CR1 HR1,NG 0 2)::
(makeTM BR1 DL1 CR0 DR1 AL1 CR1 EL1 AL0 HR1 CR0,NG 0 5)::
(makeTM BR1 DL1 CR0 ER0 CL1 AR1 BR1 DL0 HR1 AR1,NG 0 3)::
(makeTM BR1 DL1 CR0 ER0 CL1 AR1 BR1 DL0 HR1 BL1,NG 0 3)::
(makeTM BR1 DL1 CR0 ER0 DL0 AL0 AL0 BR1 BR0 HR1,NG 0 2)::
(makeTM BR1 DL1 CR0 ER0 DL0 CR0 AL0 BR1 BR0 HR1,NG 0 2)::
(makeTM BR1 DL1 CR0 ER0 DL0 EL0 AL0 BR1 BR0 HR1,NG 0 2)::
(makeTM BR1 DL1 CR0 EL1 DL0 HR1 ER1 DL0 AL1 AR0,NG 0 11)::
(makeTM BR1 DL1 CR0 EL1 DR1 BR1 AL1 ER1 HR1 AL0,NG 0 7)::
(makeTM BR1 DL1 CR0 ER1 CL1 AR1 BR1 DL0 HR1 DR0,NG 0 3)::
(makeTM BR1 DL1 CR0 ER1 DL0 HR1 ER1 DL0 AL1 AR0,NG 0 11)::
(makeTM BR1 DL1 CL1 AR0 ER0 AR1 BL0 BL1 HR1 CR1,NG 0 3)::
(makeTM BR1 DL1 CL1 AR1 DR0 AL1 ER1 CL0 HR1 BR0,NG 0 5)::
(makeTM BR1 DL1 CL1 BL0 DL1 BL1 ER0 HR1 AR0 ER1,NG 0 3)::
(makeTM BR1 DL1 CL1 BR0 DR1 BL0 EL1 AR0 HR1 CL0,NG 0 2)::
(makeTM BR1 DL1 CL1 BR0 EL0 AR0 CL0 HR1 AL1 AR0,NG 0 3)::
(makeTM BR1 DL1 CL1 BR0 EL0 AR0 CL0 HR1 AL1 DR1,NG 0 3)::
(makeTM BR1 DL1 CL1 CL0 AR0 BL1 DR1 ER0 HR1 AR1,NG 0 2)::
(makeTM BR1 DL1 CL1 DR1 AL1 AR1 EL1 BR0 HR1 CL0,NG 0 7)::
(makeTM BR1 DL1 CL1 ER0 AL1 AR1 AL0 BL1 HR1 DR1,NG 0 2)::
(makeTM BR1 DL1 CR1 HR1 DL1 CR0 EL0 AL0 ER1 AL1,NG 0 3)::
(makeTM BR1 DL1 CR1 HR1 DL1 CR0 EL1 AL0 AR1 EL0,NG 0 3)::
(makeTM BR1 DL1 CR1 AR0 AL1 HR1 BR1 EL0 CR1 EL0,NG 0 11)::
(makeTM BR1 DL1 CR1 AR0 AL1 HR1 ER0 DL0 BL0 AL1,NG 0 11)::
(makeTM BR1 DL1 CR1 AR0 AL1 HR1 ER1 DL0 AL1 AR0,NG 0 11)::
(makeTM BR1 DL1 CR1 AR0 AL1 ER0 BR1 DL0 HR1 DR1,NG 0 4)::
(makeTM BR1 DL1 CR1 BL0 AL0 CR0 BL1 ER0 HR1 DR1,NG 0 2)::
(makeTM BR1 DL1 CR1 BL0 AL1 ER0 CR0 BL1 HR1 AR1,NG 0 6)::
(makeTM BR1 DL1 CR1 BL0 DR0 AL1 BL1 ER1 HR1 AR0,NG 0 4)::
(makeTM BR1 DL1 CR1 BL0 DR0 EL1 BL1 ER1 HR1 AR0,NG 0 4)::
(makeTM BR1 DL1 CR1 BL0 DL1 ER0 HR1 BL1 AR0 AR1,NG 0 12)::
(makeTM BR1 DL1 CR1 BR0 AL0 ER1 CL1 BR1 HR1 AL1,NG 0 3)::
(makeTM BR1 DL1 CR1 ER0 AL1 HR1 AL1 DL0 ER1 AR0,NG 0 11)::
(makeTM BR1 DL1 CR1 ER0 AL1 HR1 CR0 DL0 BL0 AR1,NG 0 12)::
(makeTM BR1 DL1 CR1 ER0 AL1 HR1 CR0 DL0 EL1 AR1,NG 0 12)::
(makeTM BR1 DL1 CR1 ER0 AL1 AR0 BL1 CL1 HR1 DL0,NG 0 5)::
(makeTM BR1 DL1 CR1 ER0 CL1 AR0 BL1 HR1 EL1 DL0,NG 0 3)::
(makeTM BR1 DL1 CR1 EL1 AL1 HR1 ER1 DL0 AL1 AR0,NG 0 11)::
(makeTM BR1 DL1 CR1 EL1 AL1 CR0 HR1 BL1 AR1 EL0,NG 0 2)::
(makeTM BR1 DL1 CR1 EL1 AL1 CR0 HR1 CL1 AR1 EL0,NG 0 4)::
(makeTM BR1 DL1 CR1 EL1 AL1 DR0 BR1 ER1 HR1 AL0,NG 0 12)::
(makeTM BR1 DL1 CR1 EL1 DL1 CR0 BL0 AL0 HR1 CL1,NG 0 5)::
(makeTM BR1 DL1 CR1 EL1 DR1 HR1 BL0 ER1 ER0 AL0,NG 0 4)::
(makeTM BR1 DL1 CR1 ER1 AL1 HR1 BR1 BL0 DL0 AR0,NG 0 11)::
(makeTM BR1 DL1 CR1 ER1 AL1 HR1 ER1 BL0 DL0 AR0,NG 0 11)::
(makeTM BR1 DL1 CR1 ER1 AL1 HR1 ER1 DL0 AL1 AR0,NG 0 11)::
(makeTM BR1 DR1 CL0 HR1 DR1 CL1 EL1 DR0 AR1 EL0,NG 0 2)::
(makeTM BR1 DR1 CL0 BL0 DR0 BL1 ER1 HR1 AR0 AL0,NG 0 2)::
(makeTM BR1 DR1 CL0 BL0 DR0 BL1 ER1 HR1 AR0 ER1,NG 0 2)::
(makeTM BR1 DR1 CL0 BR0 AL0 AL1 ER0 CL1 AR1 HR1,NG 0 2)::
(makeTM BR1 DR1 CL0 BR0 DL0 CL1 ER1 BR1 AR1 HR1,NG 0 4)::
(makeTM BR1 DR1 CL0 BR1 ER1 DL1 CL1 BR0 HR1 AR0,NG 0 4)::
(makeTM BR1 DR1 CL1 AR0 HR1 AL1 BR1 EL0 BL0 DL0,NG 0 5)::
(makeTM BR1 DR1 CL1 AR0 AL1 BL0 ER1 CR1 HR1 BR0,NG 0 6)::
(makeTM BR1 DR1 CL1 BL0 DL1 BL1 AR0 EL1 HR1 AR1,NG 0 3)::
(makeTM BR1 DR1 CL1 BL0 DR1 BL1 HR1 ER1 AR0 AL1,NG 0 11)::
(makeTM BR1 DR1 CR1 DL1 DL1 AR0 HR1 EL0 BR1 AL1,NG 0 12)::
(makeTM BR1 EL0 CL0 AR0 DR1 CL1 HR1 BR1 AL1 CR0,NG 0 2)::
(makeTM BR1 EL0 CL0 BR0 AR1 DL1 EL1 AR0 BL1 HR1,NG 0 10)::
(makeTM BR1 EL0 CL0 DR1 CR0 AL1 BL1 DR0 BL0 HR1,NG 0 3)::
(makeTM BR1 EL0 CL0 DR1 DR0 AL1 AR1 HR1 AL0 BR0,NG 0 2)::
(makeTM BR1 EL0 CR0 AL0 DL1 AR1 CL1 HR1 BL1 ER1,NG 0 2)::
(makeTM BR1 EL0 CR0 AR0 DL0 CL1 AL1 AR1 BL1 HR1,NG 0 3)::
(makeTM BR1 EL0 CR0 BR0 CL1 DR1 HR1 AL1 AR1 EL0,NG 0 3)::
(makeTM BR1 EL0 CR0 DL1 CL1 BR0 AL0 HR1 AR0 DR1,NG 0 2)::
(makeTM BR1 EL0 CL1 AR1 HR1 DL0 AL1 AL1 BR0 EL1,NG 0 4)::
(makeTM BR1 EL0 CL1 AR1 HR1 DL0 ER0 AL1 BR0 EL1,NG 0 4)::
(makeTM BR1 EL0 CL1 BR0 DL0 CL0 AL1 ER0 BR1 HR1,NG 0 3)::
(makeTM BR1 EL0 CL1 CR0 DR1 BL1 HR1 ER1 AR0 AL1,NG 0 5)::
(makeTM BR1 EL0 CL1 DR0 HR1 DL1 BR1 AR1 BL0 AL0,NG 0 5)::
(makeTM BR1 EL0 CL1 DR1 HR1 DL0 AR1 EL0 BR0 EL1,NG 0 3)::
(makeTM BR1 EL0 CL1 DR1 AL1 BL0 CL1 DR0 HR1 DL1,NG 0 4)::
(makeTM BR1 EL0 CL1 DR1 AL1 CL0 AR0 HR1 CR0 CL0,NG 0 12)::
(makeTM BR1 EL0 CL1 ER0 AL1 DL0 BL1 HR1 AR0 BR1,NG 0 5)::
(makeTM BR1 EL0 CL1 ER0 AL1 DL0 BL1 HR1 AR0 EL0,NG 0 5)::
(makeTM BR1 EL0 CL1 ER0 AL1 DL0 BL1 HR1 AR0 EL1,NG 0 5)::
(makeTM BR1 EL0 CL1 ER1 AL1 DR1 HR1 BR0 CL1 DL1,NG 0 12)::
(makeTM BR1 EL0 CR1 HR1 DL1 CR0 BL0 EL1 AR1 AL0,NG 0 3)::
(makeTM BR1 EL0 CR1 AL0 DL1 HR1 AL1 DR1 AR0 DR0,NG 0 3)::
(makeTM BR1 EL0 CR1 DL0 DL1 AR1 BL0 AR0 BL1 HR1,NG 0 2)::
(makeTM BR1 EL0 CR1 DR0 DL1 HR1 BR1 AL1 CR1 EL0,NG 0 11)::
(makeTM BR1 EL0 CR1 DR0 DL1 DR0 HR1 AR1 BL1 EL1,NG 0 5)::
(makeTM BR1 EL0 CR1 EL1 DR0 CR0 ER1 HR1 AL0 BL1,NG 0 3)::
(makeTM BR1 ER0 BL0 CL1 DL1 CR1 AR0 DL0 HR1 DR1,NG 0 4)::
(makeTM BR1 ER0 BL1 CR0 AR1 DL1 AL1 HR1 EL1 DL0,NG 0 3)::
(makeTM BR1 ER0 CL0 HR1 DL1 CL1 AR1 AL0 AR0 ER1,NG 0 3)::
(makeTM BR1 ER0 CL0 AL1 DL0 CL1 AR1 DR1 HR1 BR0,NG 0 3)::
(makeTM BR1 ER0 CL0 BR0 DL0 CL1 AR1 DR0 HR1 DR0,NG 0 3)::
(makeTM BR1 ER0 CL0 BR1 ER1 DL1 BL0 AR1 AR0 HR1,NG 0 2)::
(makeTM BR1 ER0 CR0 BL0 DR1 HR1 AL1 DL1 BL1 ER1,NG 0 2)::
(makeTM BR1 ER0 CL1 HR1 AR1 DL1 CL1 DL0 ER1 CR0,NG 0 11)::
(makeTM BR1 ER0 CL1 HR1 EL1 DL1 CL0 AL0 AR1 DR0,NG 0 3)::
(makeTM BR1 ER0 CL1 AR0 AL1 DL0 BL0 HR1 AR0 DL0,NG 0 7)::
(makeTM BR1 ER0 CL1 AR0 DL0 BL0 DR1 ER1 CR1 HR1,NG 0 8)::
(makeTM BR1 ER0 CL1 AR1 HR1 DL0 AR1 DL1 CR0 AL0,NG 0 6)::
(makeTM BR1 ER0 CL1 BL1 HR1 DL0 ER0 DL0 AR1 ER1,NG 0 4)::
(makeTM BR1 ER0 CL1 BL1 DR0 CL0 AR1 HR1 AR1 ER1,NG 0 4)::
(makeTM BR1 ER0 CL1 BL1 DR1 CL0 AL0 HR1 AR1 ER1,NG 0 4)::
(makeTM BR1 ER0 CL1 CR0 AR1 DL1 AL1 BL1 HR1 DL0,NG 0 5)::
(makeTM BR1 ER0 CL1 CL1 AR1 DL0 BL0 DR0 CR1 HR1,NG 0 5)::
(makeTM BR1 ER0 CL1 CL1 AR1 DL0 BL0 DR1 CR1 HR1,NG 0 5)::
(makeTM BR1 ER0 CL1 DR0 AL1 BL0 ER1 DR0 HR1 CL1,NG 0 4)::
(makeTM BR1 ER0 CL1 DR0 AL1 BL1 HR1 AR1 CL0 AL0,NG 0 2)::
(makeTM BR1 ER0 CL1 DR0 AL1 CL1 AR1 DL0 HR1 CL0,NG 0 5)::
(makeTM BR1 ER0 CL1 DR0 AR1 DL0 BL0 CL1 CR1 HR1,NG 0 5)::
(makeTM BR1 ER0 CL1 DR0 AR1 DL0 BL0 DR0 CR1 HR1,NG 0 5)::
(makeTM BR1 ER0 CL1 DR0 AR1 DL0 BL0 DR1 CR1 HR1,NG 0 5)::
(makeTM BR1 ER0 CL1 DR1 AL1 CL0 AR0 HR1 CL0 AL0,NG 0 4)::
(makeTM BR1 ER0 CL1 EL0 AR0 DL1 CR1 DL0 HR1 DR1,NG 0 4)::
(makeTM BR1 ER0 CR1 BL0 DL1 AR1 HR1 BL1 CL1 AR1,NG 0 2)::
(makeTM BR1 ER0 CR1 BL1 DL0 AR1 HR1 BL0 CL1 ER1,NG 0 2)::
(makeTM BR1 EL1 BL1 CR0 HR1 DR1 AL1 AR0 AR1 EL0,NG 0 4)::
(makeTM BR1 EL1 CL0 BR0 AR0 DR1 AL1 BR1 DL0 HR1,NG 0 12)::
(makeTM BR1 EL1 CL0 CR0 DR1 CR0 AL1 BR0 DL0 HR1,NG 0 12)::
(makeTM BR1 EL1 CL0 DR1 DL1 DL0 BR0 AR0 CL1 HR1,NG 0 1)::
(makeTM BR1 EL1 CL0 ER0 DL1 CL1 AL1 HR1 BR0 DL0,NG 0 7)::
(makeTM BR1 EL1 CR0 HR1 DL1 CR0 AR1 DL0 DR1 EL1,NG 0 2)::
(makeTM BR1 EL1 CR0 BR0 CL1 DR0 HR1 EL1 AR1 EL0,NG 0 3)::
(makeTM BR1 EL1 CR0 BL1 AL1 DR0 CL0 CR1 BL0 HR1,NG 0 2)::
(makeTM BR1 EL1 CR0 BL1 AL1 DR0 EL0 CR1 BL0 HR1,NG 0 2)::
(makeTM BR1 EL1 CR0 BL1 DR0 BL0 EL0 CR1 AL1 HR1,NG 0 2)::
(makeTM BR1 EL1 CR0 DR0 AL1 CR1 BL1 HR1 BL0 AL0,NG 0 5)::
(makeTM BR1 EL1 CR0 DR0 AL1 CR1 CR1 HR1 BL0 AL0,NG 0 5)::
(makeTM BR1 EL1 CR0 EL0 DL1 AR1 CL1 HR1 BL1 AL0,NG 0 2)::
(makeTM BR1 EL1 CR0 ER1 DL1 AL0 AL0 HR1 BR0 CR1,NG 0 6)::
(makeTM BR1 EL1 CL1 HR1 AR1 DL1 ER1 DL0 CL1 CR0,NG 0 11)::
(makeTM BR1 EL1 CL1 HR1 DL1 CR1 AR1 AL0 ER0 DR1,NG 0 4)::
(makeTM BR1 EL1 CL1 BR0 AL0 DL0 AR1 CL1 HR1 BL1,NG 0 5)::
(makeTM BR1 EL1 CL1 BR0 DL0 BL0 AL1 AR0 CL0 HR1,NG 0 3)::
(makeTM BR1 EL1 CL1 CR1 DL1 BR0 HR1 AL1 CR1 EL0,NG 0 2)::
(makeTM BR1 EL1 CL1 CR1 DL1 CR0 AL1 AR1 HR1 BL0,NG 0 4)::
(makeTM BR1 EL1 CL1 DR1 AL1 CL0 AR0 HR1 BR1 CR1,NG 0 12)::
(makeTM BR1 EL1 CR1 HR1 DR0 CR0 DL1 AR1 BR1 EL0,NG 0 3)::
(makeTM BR1 EL1 CR1 HR1 DL1 CR1 AR1 AL0 ER0 DR1,NG 0 4)::
(makeTM BR1 EL1 CR1 BL0 DL1 DR0 AR0 AR1 HR1 BL1,NG 0 12)::
(makeTM BR1 EL1 CR1 BL0 DR1 HR1 EL1 DR0 BL0 AL1,NG 0 2)::
(makeTM BR1 EL1 CR1 BR0 DR0 BR0 ER1 HR1 AL0 AL1,NG 0 3)::
(makeTM BR1 EL1 CR1 BR1 DR0 BR0 EL0 HR1 AL1 CL0,NG 0 3)::
(makeTM BR1 EL1 CR1 DL0 DL1 CR0 AL0 DL1 HR1 BL0,NG 0 3)::
(makeTM BR1 EL1 CR1 DR0 DL1 CR0 AL0 DL1 HR1 BL0,NG 0 3)::
(makeTM BR1 EL1 CR1 DL1 DL1 ER0 HR1 AL0 BR1 DR1,NG 0 12)::
(makeTM BR1 EL1 CR1 DR1 BL0 HR1 AL1 AR0 DR1 EL0,NG 0 11)::
(makeTM BR1 ER1 CL0 BR0 DL0 CL1 AR1 DR0 HR1 DL1,NG 0 3)::
(makeTM BR1 ER1 CL0 DL0 AR1 DL0 ER0 CL1 BR0 HR1,NG 0 2)::
(makeTM BR1 ER1 CL0 DR1 DL0 CL1 AR1 AL1 HR1 BR0,NG 0 3)::
(makeTM BR1 ER1 CL1 HR1 AR1 DL1 AR1 AL0 DL0 CR0,NG 0 11)::
(makeTM BR1 ER1 CL1 HR1 AR1 DL1 ER1 AL0 DL0 CR0,NG 0 11)::
(makeTM BR1 ER1 CL1 HR1 AR1 DL1 ER1 DL0 CL1 CR0,NG 0 11)::
(makeTM BR1 ER1 CL1 HR1 DL0 CL0 DR1 AL1 BL1 ER0,NG 0 3)::
(makeTM BR1 ER1 CL1 AR0 HR1 DL1 AL1 BL0 DR0 EL0,NG 0 3)::
(makeTM BR1 ER1 CL1 BL0 DL1 BL1 AR0 AL1 HR1 DR1,NG 0 11)::
(makeTM BR1 ER1 CL1 BL0 DL1 BL1 ER0 HR1 AR0 ER1,NG 0 3)::
(makeTM BR1 ER1 CL1 BL0 DR1 BL1 AR0 AL1 HR1 DR1,NG 0 11)::
(makeTM BR1 ER1 CL1 CR0 AR0 DL1 CR1 DL0 HR1 CR1,NG 0 4)::
(makeTM BR1 ER1 CL1 CR0 AR0 DL1 CR1 DL0 HR1 DL0,NG 0 4)::
(makeTM BR1 ER1 CL1 DL0 DL1 BL0 AR0 AR0 HR1 AR1,NG 0 3)::
(makeTM BR1 ER1 CR1 DL0 DL1 BR0 AR0 CL1 HR1 BR1,NG 0 2)::
(makeTM BR1 ER1 CR1 EL1 DL1 AR0 BR1 AL1 HR1 DL0,NG 0 12)::
nil.


Definition tm_NG2:list ((TM Σ)*(DeciderType)) :=
(makeTM BR0 HR1 CL1 AR1 DL1 AR0 ER1 CL0 DL0 ER0,NG 2 2)::
(makeTM BR0 HR1 CL1 EL0 DR1 CL1 ER1 DR0 BL1 AR1,NG 2 4)::
(makeTM BR0 HR1 CR1 CR0 DR1 CL0 EL1 AR1 CL1 EL0,NG 2 11)::
(makeTM BR0 HR1 CR1 CL1 DR1 EL1 BL1 DR0 AL1 BL0,NG 2 9)::
(makeTM BR0 AL0 CL1 DR1 AL1 CL0 ER1 DR0 BR1 HR1,NG 2 2)::
(makeTM BR0 AL0 CR1 HR1 DL1 CR0 ER1 DL0 AL1 BR1,NG 2 2)::
(makeTM BR0 AL0 CR1 HR1 DR1 CL0 EL1 ER0 AR1 CL1,NG 2 9)::
(makeTM BR0 AR0 CR1 DL1 DL1 BR1 EL0 AL0 DL0 HR1,NG 2 2)::
(makeTM BR0 AR1 CR1 AL0 DL1 ER1 BL1 DL0 BR1 HR1,NG 2 6)::
(makeTM BR0 AR1 CR1 DL0 DL1 ER1 BL1 DL0 AR1 HR1,NG 2 8)::
(makeTM BR0 BL0 CL1 AR1 DL0 CL0 ER1 BL1 DR1 HR1,NG 2 3)::
(makeTM BR0 BR1 CR0 AR0 DR1 HR1 EL1 EL0 AR1 DL1,NG 2 2)::
(makeTM BR0 BR1 CL1 AR1 DL1 DL0 EL0 CL0 AL1 HR1,NG 2 2)::
(makeTM BR0 CL0 CL1 BR0 DR1 CL0 AR1 EL1 HR1 DL1,NG 2 2)::
(makeTM BR0 CL0 CR1 DR0 AL1 CL1 ER1 BR1 HR1 CL0,NG 2 3)::
(makeTM BR0 DL0 CL0 ER1 DR1 HR1 AL1 EL1 BL1 ER0,NG 2 6)::
(makeTM BR0 DL0 CL1 ER0 DL0 HR1 AR1 EL0 CR0 AL0,NG 2 2)::
(makeTM BR0 DL0 CR1 HR1 DL1 ER1 ER0 AL0 DL1 BR1,NG 2 4)::
(makeTM BR0 DL0 CR1 CL0 DL1 CR0 AL0 EL1 BL1 HR1,NG 2 6)::
(makeTM BR0 DL0 CR1 CL1 DL1 CR0 AL0 EL1 BL1 HR1,NG 2 5)::
(makeTM BR0 DL0 CR1 CR1 DL1 ER1 CR0 AL0 BR1 HR1,NG 2 5)::
(makeTM BR0 DL0 CR1 CR1 DL1 ER1 ER0 AL0 BR1 HR1,NG 2 6)::
(makeTM BR0 DL0 CR1 DL0 DL1 ER1 CR0 AL0 BR1 HR1,NG 2 5)::
(makeTM BR0 DL0 CR1 DL0 DL1 ER1 ER0 AL0 BR1 HR1,NG 2 6)::
(makeTM BR0 DL1 CR1 BL0 AL1 CR0 EL0 AL0 BL1 HR1,NG 2 7)::
(makeTM BR0 EL0 AL1 CR1 DR1 HR1 AL1 BR1 CR0 AL0,NG 2 4)::
(makeTM BR0 EL0 AL1 CR1 DR1 HR1 BR1 AL0 CR0 AL0,NG 2 4)::
(makeTM BR0 EL0 AL1 CR1 DR1 HR1 BR1 AL0 DR0 AL0,NG 2 5)::
(makeTM BR0 EL0 AL1 CR1 DR1 HR1 BR1 BR1 DR0 AL0,NG 2 5)::
(makeTM BR0 EL0 AL1 CR1 DR1 HR1 DL0 BR1 CR0 AL0,NG 2 4)::
(makeTM BR0 EL0 CL1 BR0 DR1 CL0 EL1 CR1 HR1 AL1,NG 2 2)::
(makeTM BR0 EL0 CR1 HR1 CL0 DR1 EL1 BR1 DR0 AL0,NG 2 4)::
(makeTM BR0 EL0 CR1 HR1 DR1 AL0 AL1 BR1 CR0 AL0,NG 2 6)::
(makeTM BR0 EL0 CR1 HR1 DR1 DR1 AL1 BR1 CR0 AL0,NG 2 6)::
(makeTM BR0 EL0 CR1 HR1 DR1 EL0 EL1 BR1 DR0 AL0,NG 2 4)::
(makeTM BR0 EL0 CR1 BL1 DR0 AR1 ER1 HR1 AL1 EL0,NG 2 12)::
(makeTM BR0 ER0 CL1 HR1 DL0 AR1 ER1 CL0 CR0 CL1,NG 2 2)::
(makeTM BR0 ER0 CR1 HR1 DL0 DL1 ER1 CL1 AR1 AR0,NG 2 2)::
(makeTM BR0 ER0 CR1 HR1 DL1 DL0 ER1 CL1 AR0 AR1,NG 2 2)::
(makeTM BR0 ER0 CR1 HR1 DR1 CL0 EL1 ER0 AR1 CL1,NG 2 12)::
(makeTM BR0 EL1 CL1 HR1 DR1 ER1 AL0 CR0 AR1 EL0,NG 2 6)::
(makeTM BR0 EL1 CL1 AR0 DL1 BR1 BR1 HR1 EL0 CL0,NG 2 2)::
(makeTM BR0 ER1 CL0 AR0 DL1 DR0 AR1 DL0 CR1 HR1,NG 2 6)::
(makeTM BR0 ER1 CL0 AR0 DL1 DR1 AR1 DL0 CR1 HR1,NG 2 5)::
(makeTM BR0 ER1 CL1 BR0 DL1 DR1 AR1 DL0 HR1 CR1,NG 2 5)::
(makeTM BR1 HR1 BL0 CR1 DL1 AR1 CR0 EL0 AR0 DL0,NG 2 4)::
(makeTM BR1 HR1 CL0 CL1 DR1 BL1 ER1 ER0 AR0 DR0,NG 2 2)::
(makeTM BR1 HR1 CL0 ER0 CL1 DL0 AL1 DR0 BR0 AL0,NG 2 2)::
(makeTM BR1 HR1 CL0 ER0 CL1 DL1 AL1 BR1 BR0 AL0,NG 2 2)::
(makeTM BR1 HR1 CR0 BR1 DR1 EL0 EL1 AR1 CL1 EL0,NG 2 8)::
(makeTM BR1 HR1 CR0 CL1 DR1 ER0 BL1 DL0 AR1 EL0,NG 2 5)::
(makeTM BR1 HR1 CR0 DR1 DR1 DR0 EL1 AR1 BL1 EL0,NG 2 10)::
(makeTM BR1 HR1 CR0 EL0 DL0 BR0 DL1 EL1 AL1 BR1,NG 2 2)::
(makeTM BR1 HR1 CR0 ER0 CL1 DL0 AR1 DL0 BR1 DR1,NG 2 5)::
(makeTM BR1 HR1 CR0 ER0 CL1 DL0 AR1 DL0 DR1 DR1,NG 2 5)::
(makeTM BR1 HR1 CR0 EL1 DL1 BR0 BL0 BR1 AL0 DL0,NG 2 2)::
(makeTM BR1 HR1 CL1 AR1 DR1 CL0 ER0 BR0 BL0 CR1,NG 2 5)::
(makeTM BR1 HR1 CL1 BL0 ER1 DL1 BL1 DR1 AR1 ER0,NG 2 3)::
(makeTM BR1 HR1 CL1 BR0 DR1 CL0 EL1 AR1 AR0 EL0,NG 2 2)::
(makeTM BR1 HR1 CL1 BR0 DR1 DL1 BR1 EL1 AL1 CL0,NG 2 9)::
(makeTM BR1 HR1 CL1 CL0 DR1 BL1 ER0 ER1 AR0 DR0,NG 2 2)::
(makeTM BR1 HR1 CL1 CR0 DR1 CL0 ER0 AR1 BL0 DR0,NG 2 6)::
(makeTM BR1 HR1 CL1 CR1 DR1 CL0 ER0 AR1 BL0 DR0,NG 2 5)::
(makeTM BR1 HR1 CL1 DR0 AL1 BR1 BR0 EL1 EL0 CL0,NG 2 2)::
(makeTM BR1 HR1 CL1 DL1 AL1 BL1 DR1 ER0 CL0 ER1,NG 2 4)::
(makeTM BR1 HR1 CL1 DR1 DL1 BL1 AL1 ER0 CL0 ER1,NG 2 4)::
(makeTM BR1 HR1 CL1 ER1 DR0 CL0 BR0 EL0 AR1 DL0,NG 2 4)::
(makeTM BR1 HR1 CL1 ER1 DL1 CL0 DR0 BR0 AR1 CR1,NG 2 6)::
(makeTM BR1 HR1 CL1 ER1 DL1 CL0 ER0 BR0 AR1 CR1,NG 2 6)::
(makeTM BR1 HR1 CL1 ER1 ER0 DL0 AR0 CL0 CL1 AR1,NG 2 4)::
(makeTM BR1 HR1 CR1 BL0 DL1 DR0 ER1 BL1 AR0 DR0,NG 2 12)::
(makeTM BR1 HR1 CR1 BL0 DL1 DR0 ER1 BL1 AR0 EL0,NG 2 9)::
(makeTM BR1 HR1 CR1 BL1 DR1 CR0 EL1 AR1 AL1 EL0,NG 2 3)::
(makeTM BR1 HR1 CR1 BL1 DR1 CR0 EL1 AR1 BL1 EL0,NG 2 3)::
(makeTM BR1 HR1 CR1 BL1 DR1 CR1 EL1 AR0 CL1 EL0,NG 2 5)::
(makeTM BR1 HR1 CR1 CR1 DL1 AR1 AR0 EL0 BR0 DL0,NG 2 6)::
(makeTM BR1 HR1 CR1 CR1 DL1 AR1 CR0 EL0 BR0 DL0,NG 2 5)::
(makeTM BR1 HR1 CR1 DL0 DL1 AR1 AR0 EL0 BR0 DL0,NG 2 6)::
(makeTM BR1 HR1 CR1 DL0 DL1 AR1 CR0 EL0 AR0 DL0,NG 2 4)::
(makeTM BR1 HR1 CR1 DL0 DL1 AR1 CR0 EL0 BR0 DL0,NG 2 5)::
(makeTM BR1 HR1 CR1 EL0 DR1 AR0 BL1 DR1 DL0 EL0,NG 2 3)::
(makeTM BR1 AL0 CL0 DR0 BL1 AL1 CR0 ER1 DR1 HR1,NG 2 7)::
(makeTM BR1 AL0 CL0 DR1 AL1 CR0 ER0 BR0 CR1 HR1,NG 2 7)::
(makeTM BR1 AL0 CR0 HR1 CL1 DR1 ER1 AL1 BR0 CR0,NG 2 10)::
(makeTM BR1 AL0 CR0 EL0 DL1 BR0 AL1 HR1 DR1 DL1,NG 2 2)::
(makeTM BR1 AL0 CR0 ER0 CL1 DR1 BR1 AL1 HR1 DR0,NG 2 3)::
(makeTM BR1 AL0 CR0 ER1 DL0 BR0 AL1 AR0 DR1 HR1,NG 2 6)::
(makeTM BR1 AL0 CR0 ER1 DL0 BR0 AL1 AR1 DR1 HR1,NG 2 5)::
(makeTM BR1 AL0 CR0 ER1 DL1 CR0 AL1 AR1 HR1 DR1,NG 2 5)::
(makeTM BR1 AL0 CL1 HR1 AL1 DR1 AR1 ER0 CL1 CR1,NG 2 7)::
(makeTM BR1 AL0 CL1 HR1 AL1 DR1 BR0 ER0 DL0 CR1,NG 2 9)::
(makeTM BR1 AL0 CL1 HR1 ER0 DL0 CL0 BR0 ER1 AR0,NG 2 2)::
(makeTM BR1 AL0 CL1 AR1 HR1 DL1 ER0 CL0 AL1 ER0,NG 2 2)::
(makeTM BR1 AL0 CL1 BR0 AR0 DL1 EL0 CL0 AL1 HR1,NG 2 7)::
(makeTM BR1 AL0 CL1 BR0 DR1 BL1 HR1 ER1 AL0 DR0,NG 2 2)::
(makeTM BR1 AL0 CL1 BR0 EL1 DR1 HR1 CR1 AL0 BR0,NG 2 2)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER0 BR1 AR1 HR1,NG 2 12)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER0 BR1 BR0 HR1,NG 2 11)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER0 CR0 AR1 HR1,NG 2 12)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER0 DL0 AR1 HR1,NG 2 12)::
(makeTM BR1 AL0 CL1 CR1 AL1 DR1 ER0 BR0 AR1 HR1,NG 2 9)::
(makeTM BR1 AL0 CL1 CR1 AL1 DR1 ER1 BR0 AR1 HR1,NG 2 7)::
(makeTM BR1 AL0 CL1 DR1 HR1 DL1 ER0 AR1 BL0 DR0,NG 2 5)::
(makeTM BR1 AL0 CR1 HR1 DR0 ER0 DL1 AL0 AR1 AR1,NG 2 5)::
(makeTM BR1 AL0 CR1 HR1 DR0 ER0 DL1 AL0 CR1 AR1,NG 2 5)::
(makeTM BR1 AL0 CR1 CL1 DL1 CR0 AL0 EL1 HR1 BL1,NG 2 5)::
(makeTM BR1 AL0 CR1 EL1 DR0 AL0 AL1 DR0 HR1 BL1,NG 2 2)::
(makeTM BR1 AR0 BL1 CR0 HR1 DL0 EL1 AR1 CR1 DL1,NG 2 2)::
(makeTM BR1 AR0 CL0 AR0 DL1 CR1 EL0 BL1 AL1 HR1,NG 2 12)::
(makeTM BR1 AR0 CR0 EL1 DL0 AR1 BL1 HR1 CL0 EL1,NG 2 9)::
(makeTM BR1 AR0 CR0 ER1 DL0 AR1 BL1 HR1 CL0 EL1,NG 2 12)::
(makeTM BR1 AR0 CL1 HR1 DL1 CR1 EL1 DL0 AR1 BL1,NG 2 3)::
(makeTM BR1 AR0 CL1 HR1 DL1 CR1 EL1 DL0 AR1 CL1,NG 2 3)::
(makeTM BR1 AR0 CL1 AR0 AR1 DL1 EL1 HR1 BL0 EL1,NG 2 9)::
(makeTM BR1 AR0 CL1 AR1 AR1 DL0 EL1 BR1 CL0 HR1,NG 2 11)::
(makeTM BR1 AR0 CL1 BR0 AR1 DL1 EL0 HR1 BL1 BL0,NG 2 11)::
(makeTM BR1 AR0 CL1 BL1 AR1 DL0 EL1 HR1 BL1 ER1,NG 2 5)::
(makeTM BR1 AR0 CL1 DR1 DL1 CL0 ER1 HR1 AR1 EL1,NG 2 3)::
(makeTM BR1 AR0 CL1 EL0 DL1 CL0 AR1 BL1 HR1 AR1,NG 2 3)::
(makeTM BR1 AR0 CL1 ER1 DL1 BL0 AR1 DL1 CR0 HR1,NG 2 4)::
(makeTM BR1 AR0 CL1 ER1 DL1 CL0 AL1 HR1 AR1 EL1,NG 2 3)::
(makeTM BR1 AR0 CR1 HR1 DL1 CL0 AR1 EL1 CL1 ER1,NG 2 3)::
(makeTM BR1 AL1 AL0 CR0 DL0 BR0 EL1 HR1 DL1 CR1,NG 2 2)::
(makeTM BR1 AL1 CR0 ER1 DR1 HR1 EL1 DL0 AR0 DL0,NG 2 12)::
(makeTM BR1 AL1 CR1 BR0 DL1 AR1 EL1 DL0 AR1 HR1,NG 2 4)::
(makeTM BR1 AL1 CR1 BR0 DL1 AR1 EL1 DL0 BL1 HR1,NG 2 4)::
(makeTM BR1 AL1 CR1 BR0 DL1 ER1 AL1 CL0 DR0 HR1,NG 2 4)::
(makeTM BR1 AL1 CR1 BR0 DR1 HR1 EL1 AR1 AL1 EL0,NG 2 5)::
(makeTM BR1 AL1 CR1 EL1 DR1 AL0 CL0 DR0 HR1 BL0,NG 2 3)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL0 ER1 HR1 AR1 EL1,NG 2 5)::
(makeTM BR1 AR1 CL1 DR1 BR0 CL0 AL1 EL1 HR1 DL0,NG 2 8)::
(makeTM BR1 AR1 CL1 EL0 DL1 BL0 AR1 AL0 HR1 AR0,NG 2 4)::
(makeTM BR1 BL0 CR0 BR1 DL1 CR0 EL0 HR1 AL1 CL0,NG 2 2)::
(makeTM BR1 BL0 CL1 BR0 EL0 DL1 AL1 HR1 AR0 CL0,NG 2 6)::
(makeTM BR1 BL0 CL1 ER0 HR1 DL0 AL1 EL0 AR1 BR1,NG 2 2)::
(makeTM BR1 BL0 CL1 ER1 DL0 CR0 EL1 HR1 AL1 ER0,NG 2 9)::
(makeTM BR1 BL0 CR1 AR0 DL0 ER1 BL1 DL1 HR1 AR1,NG 2 5)::
(makeTM BR1 BR0 CR0 AR0 DR1 HR1 EL0 EL1 AR1 DL1,NG 2 2)::
(makeTM BR1 BR0 CL1 AR1 DL0 DL1 EL0 CL0 AL1 HR1,NG 2 2)::
(makeTM BR1 BR0 CR1 BL0 DL1 ER1 BL1 DL0 AR0 HR1,NG 2 11)::
(makeTM BR1 BL1 CL1 BR0 EL0 DL1 AL1 HR1 AR0 CL0,NG 2 5)::
(makeTM BR1 BL1 CR1 DL1 AL1 CR0 EL0 AL0 CL1 HR1,NG 2 9)::
(makeTM BR1 BL1 CR1 DL1 AL1 CR0 EL1 AL0 AR0 HR1,NG 2 9)::
(makeTM BR1 BL1 CR1 DL1 AL1 CR0 EL1 AL0 CL1 HR1,NG 2 8)::
(makeTM BR1 BL1 CR1 DL1 AL1 CR0 EL1 AL0 CR1 HR1,NG 2 9)::
(makeTM BR1 BR1 CL1 ER1 BR0 DL0 AR0 CL0 AR1 HR1,NG 2 5)::
(makeTM BR1 BR1 CL1 ER1 ER0 DL0 AR0 CL0 AR1 HR1,NG 2 6)::
(makeTM BR1 BR1 CR1 BL0 DR1 HR1 ER0 AR0 EL1 BL0,NG 2 6)::
(makeTM BR1 CL0 CR0 EL0 DL1 CR0 AL1 HR1 AR1 EL0,NG 2 2)::
(makeTM BR1 CL0 CL1 DR1 AL1 CL0 ER1 HR1 AR0 ER1,NG 2 8)::
(makeTM BR1 CL0 CL1 ER1 BR0 DL0 AR0 CL0 AR1 HR1,NG 2 5)::
(makeTM BR1 CL0 CL1 ER1 BR0 DL0 ER0 CL0 AR1 HR1,NG 2 4)::
(makeTM BR1 CL0 CL1 ER1 ER0 DL0 AR0 CL0 AR1 HR1,NG 2 6)::
(makeTM BR1 CR0 CR1 BL0 DL1 ER1 HR1 BL1 AR1 EL1,NG 2 3)::
(makeTM BR1 CL1 AL0 DR1 AL1 ER1 HR1 AL0 BR0 ER0,NG 2 2)::
(makeTM BR1 CL1 AL0 ER0 DL1 HR1 AL1 AL1 DL0 BR0,NG 2 5)::
(makeTM BR1 CL1 AL0 ER0 DL1 HR1 AL1 BR0 CL0 BR0,NG 2 4)::
(makeTM BR1 CL1 AL0 ER0 DL1 HR1 AL1 BR0 DL0 BR0,NG 2 5)::
(makeTM BR1 CL1 AL0 ER0 DL1 HR1 BR1 AL1 CL0 BR0,NG 2 4)::
(makeTM BR1 CL1 AL0 ER0 DL1 HR1 DR0 AL1 CL0 BR0,NG 2 4)::
(makeTM BR1 CL1 CL0 ER0 BR1 DL1 AL1 HR1 DL0 BR0,NG 2 4)::
(makeTM BR1 CL1 CL1 HR1 ER0 DL0 CL0 BR0 ER1 AR1,NG 2 2)::
(makeTM BR1 CL1 CR1 BR0 DL1 HR1 EL1 DR1 AL1 EL0,NG 2 3)::
(makeTM BR1 CL1 CR1 ER0 AL1 DL1 BL0 HR1 DL0 BR0,NG 2 5)::
(makeTM BR1 CR1 CL1 HR1 DR1 CL0 ER0 AR1 BL1 ER0,NG 2 7)::
(makeTM BR1 DL0 CR1 AL1 AL1 HR1 AL0 ER1 ER0 BR0,NG 2 2)::
(makeTM BR1 DL0 CR1 CR0 AL1 ER0 DL0 CL0 BR0 HR1,NG 2 4)::
(makeTM BR1 DR0 CL1 BL1 AR0 BL0 ER1 AR1 HR1 BL0,NG 2 3)::
(makeTM BR1 DR0 CL1 BL1 DR1 BL0 EL0 AR1 CR0 HR1,NG 2 12)::
(makeTM BR1 DR0 CL1 BR1 DL1 CL0 AR1 EL1 AL0 HR1,NG 2 4)::
(makeTM BR1 DR0 CL1 CR0 ER1 DL0 BL1 CL1 HR1 AR0,NG 2 2)::
(makeTM BR1 DR0 CL1 ER1 AR1 CL1 HR1 CL0 DL0 AR0,NG 2 3)::
(makeTM BR1 DR0 CR1 EL0 DL1 AR1 HR1 EL1 BR0 BL0,NG 2 5)::
(makeTM BR1 DL1 CR0 AR0 DR1 HR1 ER1 DL0 AL1 AR0,NG 2 12)::
(makeTM BR1 DL1 CR0 BL0 DR1 HR1 ER1 DL0 AL1 AR0,NG 2 12)::
(makeTM BR1 DL1 CR0 ER0 CL1 AL0 AL1 AL0 HR1 BR0,NG 2 2)::
(makeTM BR1 DL1 CR0 ER0 CL1 AR1 BR1 DL0 HR1 AR0,NG 2 3)::
(makeTM BR1 DL1 CR0 ER1 DR1 HR1 ER1 DL0 AL1 AR0,NG 2 12)::
(makeTM BR1 DL1 CL1 HR1 DR1 BL1 EL0 DR0 CR1 AL0,NG 2 5)::
(makeTM BR1 DL1 CL1 AR1 EL0 DR1 HR1 BR0 AL1 CL1,NG 2 11)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL0 CL0 AR1 HR1,NG 2 9)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL0 CL0 BR0 HR1,NG 2 8)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL0 CL0 BL1 HR1,NG 2 9)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL0 CL0 CR0 HR1,NG 2 9)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL1 CL0 AR1 HR1,NG 2 8)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL1 CL0 BL1 HR1,NG 2 8)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL1 CL0 BR1 HR1,NG 2 9)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL1 CL0 CL0 HR1,NG 2 8)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL1 CL0 CR0 HR1,NG 2 9)::
(makeTM BR1 DL1 CL1 BR0 AR1 AL1 EL1 CL0 DR0 HR1,NG 2 9)::
(makeTM BR1 DL1 CR1 BR0 AL0 CR0 EL1 DL0 AL1 HR1,NG 2 2)::
(makeTM BR1 DL1 CR1 BR0 CL1 AL0 EL1 CR1 AL1 HR1,NG 2 2)::
(makeTM BR1 DL1 CR1 BR0 DL0 DR1 HR1 EL0 AR1 EL1,NG 2 3)::
(makeTM BR1 DL1 CR1 BR0 DL1 HR1 EL1 DR1 AL1 EL0,NG 2 3)::
(makeTM BR1 DL1 CR1 ER0 AL1 CR1 AL1 AL0 HR1 BR0,NG 2 3)::
(makeTM BR1 DL1 CR1 EL1 AL1 CR0 HR1 CL1 BR1 EL0,NG 2 5)::
(makeTM BR1 DR1 BL1 CL1 AR0 EL0 HR1 AR1 CL0 AR0,NG 2 2)::
(makeTM BR1 DR1 CR0 AR0 CL1 DL0 ER1 DL0 BR1 HR1,NG 2 5)::
(makeTM BR1 DR1 CL1 CL0 AR1 BL1 HR1 EL1 CR0 ER0,NG 2 5)::
(makeTM BR1 EL0 CL0 AR1 DL1 CL1 BR0 EL1 HR1 BR0,NG 2 2)::
(makeTM BR1 EL0 CL0 AR1 DL1 CL1 DR1 EL1 HR1 BR0,NG 2 2)::
(makeTM BR1 EL0 CR0 HR1 DL1 ER0 AL0 CR0 BL0 DR0,NG 2 2)::
(makeTM BR1 EL0 CL1 AR0 DR1 BL1 AR1 DR0 CL0 HR1,NG 2 3)::
(makeTM BR1 EL0 CL1 DR1 AL1 CL0 AR1 HR1 AR0 ER1,NG 2 6)::
(makeTM BR1 ER0 CL1 BL1 DR0 BL0 HR1 ER0 CR1 AR1,NG 2 3)::
(makeTM BR1 ER0 CL1 DR1 DR0 CL0 AR1 DL0 DR1 HR1,NG 2 4)::
(makeTM BR1 ER0 CR1 AR0 DL1 DR0 AL1 DL1 HR1 DL0,NG 2 4)::
(makeTM BR1 EL1 CR0 BR0 DL1 AR1 CL1 HR1 AL0 AR0,NG 2 3)::
(makeTM BR1 EL1 CR0 BR0 DL1 AR1 CL1 HR1 CR1 AL0,NG 2 2)::
(makeTM BR1 EL1 CR0 DR1 DR0 HR1 AL1 AR0 DR1 EL0,NG 2 11)::
(makeTM BR1 EL1 CL1 BR0 DR1 AL1 EL0 DR0 AL0 HR1,NG 2 2)::
(makeTM BR1 EL1 CL1 DR0 BR0 AL1 EL1 CR0 BL0 HR1,NG 2 11)::
(makeTM BR1 EL1 CR1 AR0 DL1 CR1 AL1 DL0 BL0 HR1,NG 2 4)::
(makeTM BR1 EL1 CR1 BR0 DR1 HR1 AL1 DL0 DL1 ER1,NG 2 3)::
(makeTM BR1 EL1 CR1 CR0 DR0 BR0 ER1 HR1 AL0 AL1,NG 2 2)::
(makeTM BR1 ER1 CL1 BR1 DL0 BL0 ER1 HR1 AR1 ER0,NG 2 10)::
nil.


Definition tm_NG3:list ((TM Σ)*(DeciderType)) :=
(makeTM BR0 HR1 CR0 BL0 DR1 EL0 CL1 AR1 CL1 EL0,NG 3 12)::
(makeTM BR0 HR1 CR0 BL0 DR1 EL0 EL1 AR1 CL1 EL0,NG 3 12)::
(makeTM BR0 HR1 CR0 DR1 DR1 EL0 CL1 AR1 CL1 EL0,NG 3 12)::
(makeTM BR0 HR1 CR0 DR1 DR1 EL0 EL1 AR1 CL1 EL0,NG 3 12)::
(makeTM BR0 HR1 CL1 ER0 DL1 AL0 BR1 BL0 BR0 ER1,NG 3 3)::
(makeTM BR0 AL0 CR1 DL0 BL1 ER1 BL1 DL0 AR0 HR1,NG 3 12)::
(makeTM BR0 AL0 CR1 DL0 DL1 ER1 BL1 DL0 AR0 HR1,NG 3 12)::
(makeTM BR0 AR1 CL1 AR0 CR0 DL1 EL1 HR1 BR1 BL0,NG 3 4)::
(makeTM BR0 AR1 CL1 AR0 DL1 EL0 BR1 BL0 BR0 HR1,NG 3 3)::
(makeTM BR0 AR1 CL1 AR0 DL1 EL1 BR1 BL0 DL1 HR1,NG 3 3)::
(makeTM BR0 AR1 CL1 EL0 DL1 HR1 EL1 BL1 AR0 BL1,NG 3 6)::
(makeTM BR0 AR1 CR1 HR1 DR0 CL0 ER1 AR0 CL1 EL1,NG 3 10)::
(makeTM BR0 AR1 CR1 DL0 DL1 ER1 BL1 DL0 AL1 HR1,NG 3 4)::
(makeTM BR0 CL0 CR1 DL0 DL1 ER1 BL1 DL0 AR1 HR1,NG 3 5)::
(makeTM BR0 CL1 CR0 BR1 DL1 AL0 EL1 HR1 AL1 CL1,NG 3 6)::
(makeTM BR0 CR1 CL1 ER0 DL1 BL1 BR1 DL0 HR1 AR1,NG 3 6)::
(makeTM BR0 CR1 CR1 DL0 BL1 ER1 BL1 DL0 AR0 HR1,NG 3 12)::
(makeTM BR0 CR1 CR1 DL0 DL1 ER1 BL1 DL0 AR0 HR1,NG 3 12)::
(makeTM BR0 DL1 CR1 HR1 DR1 CL0 EL1 ER0 AR1 CL1,NG 3 12)::
(makeTM BR1 HR1 CL0 BL1 EL1 DR0 CR1 DR0 CR1 AL1,NG 3 5)::
(makeTM BR1 HR1 CL0 BL1 EL1 DR0 CR1 DR0 DR1 AL1,NG 3 4)::
(makeTM BR1 HR1 CR0 BL0 DR1 ER0 BL1 DL1 AR0 ER1,NG 3 10)::
(makeTM BR1 HR1 CR0 DL0 DR1 EL0 EL1 AR1 CL1 EL0,NG 3 5)::
(makeTM BR1 HR1 CL1 BL1 DR1 CR1 EL1 AR0 CL1 EL0,NG 3 3)::
(makeTM BR1 HR1 CR1 BL0 DL1 DR0 ER1 BL1 AR0 CL1,NG 3 12)::
(makeTM BR1 HR1 CR1 ER1 DL0 ER1 EL0 DL1 AR1 CR0,NG 3 6)::
(makeTM BR1 AL0 CR0 HR1 CL1 DR1 ER0 AL1 AR1 AL0,NG 3 12)::
(makeTM BR1 AL0 CR0 HR1 CL1 DR1 ER0 AL1 AR1 DR1,NG 3 12)::
(makeTM BR1 AL0 CR0 HR1 CL1 DR1 ER0 EL1 AR1 AL0,NG 3 12)::
(makeTM BR1 AL0 CR0 HR1 DR1 DL1 AL1 ER0 CL0 AR1,NG 3 10)::
(makeTM BR1 AL0 CR0 HR1 DR1 DL1 AL1 ER0 EL1 AR1,NG 3 10)::
(makeTM BR1 AL0 CR0 AL1 DR1 HR1 BL1 ER0 AL1 AR1,NG 3 10)::
(makeTM BR1 AL0 CR0 AL1 DR1 HR1 BL1 ER0 EL1 AR1,NG 3 10)::
(makeTM BR1 AL0 CR0 ER0 DR0 HR1 EL1 AL1 DL1 AR1,NG 3 10)::
(makeTM BR1 AL0 CR0 ER0 DR0 HR1 EL1 AL1 EL1 AR1,NG 3 10)::
(makeTM BR1 AL0 CL1 CR0 DR1 AL1 ER0 BL1 AR1 HR1,NG 3 12)::
(makeTM BR1 AL0 CL1 DR0 AL1 BL1 HR1 ER1 BR0 CR1,NG 3 6)::
(makeTM BR1 AR0 CL0 AR0 AR1 DL1 BL1 EL0 BL1 HR1,NG 3 4)::
(makeTM BR1 AR0 CL0 AR0 AR1 DL1 BL1 EL0 CL1 HR1,NG 3 4)::
(makeTM BR1 AR0 CL1 AR0 AR1 DL1 EL0 HR1 BL0 CL1,NG 3 12)::
(makeTM BR1 AR0 CL1 AR0 AR1 DL1 EL0 HR1 BL0 ER0,NG 3 12)::
(makeTM BR1 AR0 CL1 AR0 AR1 DL1 EL1 HR1 BL0 CR0,NG 3 5)::
(makeTM BR1 AR0 CL1 AR0 AR1 DL1 ER1 HR1 BL0 EL1,NG 3 4)::
(makeTM BR1 AR0 CL1 AR0 BR1 DL1 EL0 HR1 BL0 CL1,NG 3 12)::
(makeTM BR1 AR0 CL1 AR0 BR1 DL1 EL0 HR1 BL0 ER0,NG 3 12)::
(makeTM BR1 AR0 CL1 BL1 AR1 DL0 EL1 HR1 BR1 ER1,NG 3 3)::
(makeTM BR1 AR0 CR1 BL1 DL1 AR1 AL1 EL0 HR1 CL1,NG 3 3)::
(makeTM BR1 AL1 CL1 AR0 HR1 DL0 EL1 EL0 BR1 BL1,NG 3 10)::
(makeTM BR1 AR1 CL0 BR0 AL1 DL0 EL0 DL1 BL1 HR1,NG 3 10)::
(makeTM BR1 AR1 CL1 BL1 ER1 DL0 AL1 HR1 BR1 ER0,NG 3 3)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL0 ER1 HR1 AL1 EL1,NG 3 3)::
(makeTM BR1 AR1 CL1 DR0 AR1 BL0 BL1 ER0 HR1 CR0,NG 3 6)::
(makeTM BR1 BL0 CL1 ER0 AL1 DL0 BR0 HR1 BR0 ER1,NG 3 3)::
(makeTM BR1 BL0 CL1 ER0 AL1 DL1 AL1 HR1 BR0 ER1,NG 3 3)::
(makeTM BR1 BL0 CL1 ER0 CR0 DL1 AL1 HR1 BR0 ER1,NG 3 4)::
(makeTM BR1 BL1 CL1 ER0 HR1 DL0 AL1 AL0 BR1 AL1,NG 3 11)::
(makeTM BR1 BL1 CL1 ER0 HR1 DL0 AL1 AL0 BR1 EL1,NG 3 10)::
(makeTM BR1 CL0 AL1 DR1 AL1 CL0 ER0 HR1 AR0 BR1,NG 3 12)::
(makeTM BR1 CL0 AL1 DR1 AL1 CL0 ER0 HR1 AR0 EL0,NG 3 12)::
(makeTM BR1 CL0 CR0 CR1 DL0 DR1 EL1 AR0 HR1 AL1,NG 3 3)::
(makeTM BR1 CL0 CL1 BR1 DR1 AL1 ER1 CR0 HR1 DR0,NG 3 2)::
(makeTM BR1 CL0 CL1 DR1 AL1 CL0 ER0 HR1 AR0 BR1,NG 3 12)::
(makeTM BR1 CL0 CL1 DR1 AL1 CL0 ER0 HR1 AR0 EL0,NG 3 12)::
(makeTM BR1 CL0 CL1 DR1 AL1 CL0 EL1 HR1 AR0 ER1,NG 3 4)::
(makeTM BR1 CL0 CL1 DR1 AL1 CL0 ER1 HR1 AR0 BL0,NG 3 5)::
(makeTM BR1 CL1 AL1 ER0 DL0 HR1 BL0 AL1 BR1 ER0,NG 3 12)::
(makeTM BR1 CL1 AL1 ER0 DL0 HR1 BL0 DR0 BR1 ER0,NG 3 12)::
(makeTM BR1 DL0 CL1 AR0 AL1 CL1 AR1 EL0 HR1 BL0,NG 3 6)::
(makeTM BR1 DL0 CR1 AR1 AL1 CR0 HR1 EL1 AL0 BL1,NG 3 6)::
(makeTM BR1 DL0 CR1 AR1 DR1 HR1 EL0 DR0 BL0 EL1,NG 3 4)::
(makeTM BR1 DL0 CR1 DL1 DR0 CR0 EL0 BL1 AL0 HR1,NG 3 3)::
(makeTM BR1 DL0 CR1 ER0 AL1 AR0 AL0 DL1 AL0 HR1,NG 3 3)::
(makeTM BR1 DL0 CR1 ER1 AL1 AR0 AL0 DL1 CR1 HR1,NG 3 3)::
(makeTM BR1 DR0 CR1 HR1 DR1 AR1 EL0 AR1 AL0 EL1,NG 3 6)::
(makeTM BR1 DL1 CR0 EL1 DR1 HR1 ER1 DL0 AL1 AR0,NG 3 12)::
(makeTM BR1 DR1 CL0 DR1 DL0 CL1 ER1 BR0 AR1 HR1,NG 3 6)::
(makeTM BR1 EL0 BL0 CR1 DR1 HR1 AL1 AR0 AL0 EL1,NG 3 4)::
(makeTM BR1 EL0 CR1 AL0 DL1 BR0 BL1 DL1 HR1 CL0,NG 3 6)::
(makeTM BR1 ER0 CL0 ER1 CL1 DL1 AL1 HR1 BL0 AR0,NG 3 2)::
(makeTM BR1 ER0 CL1 BL0 DL1 CR1 AR1 BL1 HR1 DR1,NG 3 3)::
(makeTM BR1 EL1 CL1 AR0 HR1 DL0 EL1 EL0 BR1 BL1,NG 3 11)::
(makeTM BR1 EL1 CR1 HR1 DR0 DL0 EL0 BR0 AL0 BL0,NG 3 4)::
(makeTM BR1 EL1 CR1 DL0 DL0 CR0 AR1 DL1 HR1 AL0,NG 3 5)::
(makeTM BR1 ER1 CL1 CR0 AR1 DL0 CL0 DL1 HR1 AR1,NG 3 3)::
(makeTM BR1 ER1 CL1 CR0 AR1 DL0 CL0 DL1 HR1 CR1,NG 3 3)::
(makeTM BR1 ER1 CL1 CR0 AR1 DL0 CL0 DL1 HR1 DR0,NG 3 3)::
nil.


Definition tm_NG4:list ((TM Σ)*(DeciderType)) :=
(makeTM BR0 HR1 CL0 EL1 DL1 AL1 ER1 BR1 BL1 DR0,NG 4 6)::
(makeTM BR0 HR1 CR0 ER1 DR1 AR1 EL1 BL1 BR1 DL0,NG 4 6)::
(makeTM BR0 HR1 CL1 DR0 DL1 EL0 BR1 AL1 EL1 BL0,NG 4 2)::
(makeTM BR0 HR1 CL1 ER1 DL0 BL1 AL1 CL1 CR1 ER0,NG 4 4)::
(makeTM BR0 HR1 CR1 DL0 DL1 ER0 BL0 EL0 BL1 AR1,NG 4 7)::
(makeTM BR0 HR1 CR1 EL0 DR1 CL0 BL1 AR0 CR1 CL0,NG 4 12)::
(makeTM BR0 HR1 CR1 EL0 DR1 CL0 BL1 AR1 AR1 CL0,NG 4 7)::
(makeTM BR0 BR1 CR1 DL0 DL1 ER1 BL1 AL1 AR1 HR1,NG 4 2)::
(makeTM BR0 DR0 CL1 AR0 AR1 DL0 BR1 EL1 BL0 HR1,NG 4 7)::
(makeTM BR0 DR1 CR1 AR1 DL0 HR1 AR1 EL1 AL1 EL0,NG 4 4)::
(makeTM BR0 DR1 CR1 ER1 DL1 AL1 AR1 CL0 AL0 HR1,NG 4 6)::
(makeTM BR0 DR1 CR1 ER1 DL1 AL1 AR1 CL0 AR0 HR1,NG 4 6)::
(makeTM BR0 DR1 CR1 ER1 DL1 AL1 AR1 CL0 AR1 HR1,NG 4 5)::
(makeTM BR1 HR1 CR0 CR1 DR1 EL0 EL1 AR1 CL1 BL1,NG 4 2)::
(makeTM BR1 HR1 CL1 EL0 DR1 DL0 AR1 EL1 ER0 CR1,NG 4 4)::
(makeTM BR1 AL0 CR0 HR1 DR1 EL1 CL1 ER0 EL1 AR1,NG 4 8)::
(makeTM BR1 AL0 CR0 EL1 DR1 HR1 BL1 ER0 EL1 AR1,NG 4 8)::
(makeTM BR1 AL0 CL1 ER0 AR1 DL0 AR1 AL0 CR0 HR1,NG 4 12)::
(makeTM BR1 AL0 CL1 ER1 AR1 DL0 ER1 AL0 CR0 HR1,NG 4 7)::
(makeTM BR1 AR0 CL0 EL1 DL1 BL1 ER0 HR1 BL1 AR1,NG 4 4)::
(makeTM BR1 AR0 CL1 EL0 AR1 DL0 ER1 HR1 BL1 ER0,NG 4 6)::
(makeTM BR1 AR0 CL1 EL0 AR1 DL1 EL0 HR1 BL1 ER0,NG 4 6)::
(makeTM BR1 BL0 CR1 BL0 DL1 ER0 BR1 AL0 DR0 HR1,NG 4 12)::
(makeTM BR1 CL0 CL1 DR0 AL0 DL0 AL1 ER1 AR0 HR1,NG 4 7)::
(makeTM BR1 CL0 CL1 ER1 AL1 DL1 AR0 AR1 DR1 HR1,NG 4 2)::
(makeTM BR1 CL0 CR1 ER0 AL1 DR1 AL0 HR1 ER1 AR0,NG 4 2)::
(makeTM BR1 DL0 CR0 HR1 DR1 AL0 ER1 DL0 CL1 BR1,NG 4 7)::
(makeTM BR1 DL0 CR0 AR1 DR1 ER0 AL1 BL1 CR0 HR1,NG 4 2)::
(makeTM BR1 DL0 CR0 AR1 DR1 ER1 AL1 BL1 BL0 HR1,NG 4 6)::
(makeTM BR1 DL0 CR0 AR1 DR1 ER1 AL1 BL1 BR0 HR1,NG 4 6)::
(makeTM BR1 DL0 CR1 BL0 AL1 ER0 BR1 BL0 AR0 HR1,NG 4 12)::
(makeTM BR1 DL0 CR1 BL0 AL1 ER1 ER1 BL0 AR0 HR1,NG 4 7)::
(makeTM BR1 DR0 CL1 ER1 AR1 BL0 DR1 CR0 CL0 HR1,NG 4 2)::
(makeTM BR1 DR0 CL1 ER1 DL1 BL0 DR1 AR0 CL0 HR1,NG 4 2)::
(makeTM BR1 EL0 CR0 HR1 CL1 DR1 AR1 EL1 DR1 AL0,NG 4 11)::
(makeTM BR1 EL0 CL1 DR0 AL1 CR0 CL1 CR0 BL0 HR1,NG 4 12)::
(makeTM BR1 ER0 CL1 DR0 AL1 CL0 EL1 HR1 AR1 EL0,NG 4 6)::
(makeTM BR1 ER0 CL1 DR1 AL1 CL0 ER0 HR1 AR1 EL0,NG 4 6)::
(makeTM BR1 EL1 CR0 AR1 DR1 BR1 AL0 HR1 BL1 EL0,NG 4 4)::
(makeTM BR1 EL1 CL1 DR0 AL1 CR0 EL1 CR0 BL0 HR1,NG 4 7)::
(makeTM BR1 ER1 CL0 HR1 ER1 DL1 EL1 DL0 AR0 CR1,NG 4 4)::
(makeTM BR1 ER1 CL1 AR0 AR1 DL1 EL1 HR1 BL0 BL1,NG 4 2)::
nil.


Definition tm_NG5:list ((TM Σ)*(DeciderType)) :=
(makeTM BR0 HR1 CR1 EL0 DR1 CL0 BL1 AR0 CR1 DR0,NG 5 11)::
(makeTM BR0 HR1 CR1 EL0 DR1 CL0 BL1 AR1 AR1 DR0,NG 5 7)::
(makeTM BR0 AR1 CR1 DL1 DR1 AR0 BL1 ER1 HR1 BL0,NG 5 2)::
(makeTM BR0 DL1 CR1 AR1 AL1 HR1 EL1 BR1 AL1 EL0,NG 5 4)::
(makeTM BR0 DR1 CR1 DR1 DL1 HR1 AR1 EL0 DL1 AL1,NG 5 4)::
(makeTM BR1 HR1 CL0 ER1 DL0 CL1 AR1 BR0 DR0 DL1,NG 5 3)::
(makeTM BR1 HR1 CL1 ER1 DL1 CR0 AL1 EL0 BL1 CR1,NG 5 10)::
(makeTM BR1 HR1 CR1 BR0 CL0 DL0 AR1 EL1 AL1 BL1,NG 5 2)::
(makeTM BR1 AL0 CR0 HR1 CL1 DR1 ER0 AL1 AR1 BL1,NG 5 11)::
(makeTM BR1 AL0 CR0 HR1 DR1 HR1 DL0 ER0 EL1 AR1,NG 5 8)::
(makeTM BR1 AL0 CR0 HR1 DR1 ER0 CL0 ER0 EL1 AR1,NG 5 8)::
(makeTM BR1 AL0 CR0 ER0 DR1 HR1 BL0 ER0 EL1 AR1,NG 5 8)::
(makeTM BR1 AL0 CL1 ER0 AR1 DL0 AR1 BR0 CR0 HR1,NG 5 11)::
(makeTM BR1 AL0 CL1 ER1 AR1 DL0 ER1 BR0 CR0 HR1,NG 5 7)::
(makeTM BR1 AL0 CR1 ER0 DL1 HR1 AR1 EL1 DR1 AL1,NG 5 10)::
(makeTM BR1 CR0 CR1 BL0 DL1 ER0 BR1 AL0 DR0 HR1,NG 5 11)::
(makeTM BR1 CL1 CR1 ER0 AL1 DR1 HR1 AL0 AR0 ER1,NG 5 2)::
(makeTM BR1 DL0 CR1 BL0 AL1 ER0 BR1 CR0 AR0 HR1,NG 5 11)::
(makeTM BR1 DL0 CR1 BL0 AL1 ER1 ER1 CR0 AR0 HR1,NG 5 7)::
(makeTM BR1 DR0 CL1 HR1 ER1 DL1 CR1 EL1 AR1 EL0,NG 5 10)::
(makeTM BR1 DR1 CL1 ER0 DL1 CL0 BR0 AR1 AR1 HR1,NG 5 11)::
(makeTM BR1 EL0 CL1 DR0 AL1 CR0 CL1 AL0 BL0 HR1,NG 5 11)::
(makeTM BR1 ER0 CR0 HR1 DR1 AL0 ER1 DL0 CL1 BR1,NG 5 7)::
(makeTM BR1 EL1 CL1 AR1 AL1 DL0 BL0 DL1 HR1 BR0,NG 5 5)::
(makeTM BR1 EL1 CL1 DR0 AL1 CR0 EL1 AL0 BL0 HR1,NG 5 7)::
(makeTM BR1 EL1 CR1 HR1 DR1 CR0 DL0 AL0 BL1 CL1,NG 5 2)::
nil.

Definition tm_NG6:list ((TM Σ)*(DeciderType)) :=
(makeTM BR0 HR1 CL0 ER1 DL1 CR0 EL0 DL0 AR1 BR1,NG 6 2)::
(makeTM BR0 HR1 CL1 ER0 DL1 CL0 BR1 EL0 BR1 AL1,NG 6 3)::
(makeTM BR0 AL0 CR1 BR1 CL1 DL1 EL1 AR0 AL1 HR1,NG 6 2)::
(makeTM BR0 AR1 CL1 CR0 DL0 DR1 ER1 AL0 AR1 HR1,NG 6 4)::
(makeTM BR0 AR1 CL1 DL0 DL1 HR1 AR0 EL0 BL0 BL1,NG 6 12)::
(makeTM BR0 BL1 CL1 DR0 DL1 HR1 EL0 DL1 AR1 AL0,NG 6 4)::
(makeTM BR0 BR1 CR1 DR0 DR1 HR1 EL0 AR0 BL0 EL1,NG 6 12)::
(makeTM BR0 DL1 CR1 BL0 DR0 CR0 EL1 AL1 AL0 HR1,NG 6 2)::
(makeTM BR0 DR1 CR1 ER1 DL1 AL1 AR1 CL0 CR0 HR1,NG 6 4)::
(makeTM BR0 EL0 CR0 BR1 DL1 AL0 AL1 HR1 CL0 CL1,NG 6 12)::
(makeTM BR0 ER1 CL1 BR0 DL1 DR0 AR1 DL0 HR1 CR1,NG 6 5)::
(makeTM BR1 HR1 CL0 BR0 DL1 CL1 DR1 ER1 AR1 BL0,NG 6 2)::
(makeTM BR1 HR1 CR0 BR1 DL1 DR0 EL0 ER1 AR1 BL0,NG 6 4)::
(makeTM BR1 HR1 CR1 CL0 DL0 AR0 ER0 DL1 ER1 CL0,NG 6 4)::
(makeTM BR1 AL0 CR0 AL1 DR1 HR1 BL1 ER0 AR1 AL1,NG 6 12)::
(makeTM BR1 AL0 CR0 AL1 DR1 HR1 EL1 ER0 AR1 AL1,NG 6 12)::
(makeTM BR1 AL0 CR0 BR0 DL1 EL1 EL0 HR1 AR0 CL1,NG 6 3)::
(makeTM BR1 AL0 CR0 ER1 DL1 CR0 AL1 AR0 HR1 DR1,NG 6 4)::
(makeTM BR1 AL0 CR1 HR1 DR0 EL1 ER1 AR0 CL1 AL0,NG 6 11)::
(makeTM BR1 AL0 CR1 CL0 DL1 CR0 AL0 EL1 HR1 BL1,NG 6 5)::
(makeTM BR1 AR0 CL1 DR0 AR1 DL0 CL1 ER1 CL0 HR1,NG 6 3)::
(makeTM BR1 AR1 BL1 CL1 DL1 ER0 EL1 HR1 AR0 EL0,NG 6 2)::
(makeTM BR1 BL0 CR0 CL1 DL1 ER0 EL1 HR1 AL0 EL1,NG 6 4)::
(makeTM BR1 BL0 CL1 CR1 DL1 CR0 EL0 CR1 AL1 HR1,NG 6 12)::
(makeTM BR1 CL0 CR1 HR1 DL0 CR0 EL1 DL1 ER1 AR1,NG 6 2)::
(makeTM BR1 CL0 CR1 HR1 DR0 CR1 EL1 ER0 AL0 AR1,NG 6 4)::
(makeTM BR1 CR0 CR1 HR1 DL0 ER0 AL0 DL1 AR0 AR1,NG 6 12)::
(makeTM BR1 CL1 AL1 DR0 BL1 HR1 CL0 EL1 DR1 BR0,NG 6 4)::
(makeTM BR1 DL0 CR0 AR1 DR1 ER1 AL1 BL1 DR0 HR1,NG 6 5)::
(makeTM BR1 DL0 CL1 DR0 AL1 CL0 BR1 EL1 BR0 HR1,NG 6 3)::
(makeTM BR1 DL0 CR1 BR0 AL1 DR0 AL1 ER1 AL0 HR1,NG 6 3)::
(makeTM BR1 DR0 CL0 AR1 AL1 DL0 EL1 DR0 BL1 HR1,NG 6 11)::
(makeTM BR1 EL1 CL1 AR0 DL1 CL0 BR1 AL0 BR0 HR1,NG 6 3)::
nil.

Definition tm_NG7:list ((TM Σ)*(DeciderType)) :=
(makeTM BR0 AL0 CL1 DR0 AL1 ER1 HR1 BR1 BL1 CR1,NG 7 2)::
(makeTM BR0 AR1 CL1 CR0 DL0 DR1 ER1 AL0 AL1 HR1,NG 7 4)::
(makeTM BR0 BL1 CL1 DR0 DR1 HR1 EL0 DL1 AR1 AL0,NG 7 4)::
(makeTM BR1 HR1 CL0 BL1 DR1 DL0 ER0 EL1 AL1 BR0,NG 7 4)::
(makeTM BR1 HR1 CL0 ER0 DL0 CL1 AR1 BR0 DR0 DR1,NG 7 10)::
(makeTM BR1 AL0 CR0 HR1 BL1 DR1 DL0 ER0 EL1 AR1,NG 7 8)::
(makeTM BR1 AL0 CR0 HR1 CL1 DR1 ER1 AL1 BR0 DL0,NG 7 10)::
(makeTM BR1 AL0 CR0 HR1 DR1 DL1 AL1 ER0 AR1 CL0,NG 7 11)::
(makeTM BR1 AL0 CR0 HR1 DR1 ER1 DL1 CL1 BR1 AL1,NG 7 2)::
(makeTM BR1 BL0 CR0 CL1 DL1 ER0 ER1 HR1 AL0 EL1,NG 7 4)::
(makeTM BR1 CL0 CL1 HR1 DR0 CR1 EL1 ER0 AL0 AR1,NG 7 4)::
(makeTM BR1 DL0 CR1 EL1 AL0 CR0 HR1 AL1 AR1 BL1,NG 7 2)::
(makeTM BR1 EL1 CR0 HR1 DR1 AR1 DL1 CL1 BR1 EL0,NG 7 2)::
nil.

Definition tm_Ha:=
(makeTM BR0 HR1 CR0 BR1 DR1 EL0 CL1 AR1 CL1 BL1,Ha)::
(makeTM BR0 HR1 CR0 BR1 DR1 EL0 EL1 AR1 CL1 BL1,Ha)::
(makeTM BR0 HR1 CL1 ER0 DL0 CL1 AR1 BL0 DL0 DR1,Ha)::
(makeTM BR0 HR1 CR1 BR1 DR0 AR1 DL1 ER1 BL1 EL0,Ha)::
(makeTM BR0 HR1 CR1 DL0 DR1 ER0 BL1 DL0 ER1 AR1,Ha)::
(makeTM BR0 HR1 CR1 DR0 DL1 ER0 EL0 DL0 AR1 BL0,Ha)::
(makeTM BR0 HR1 CR1 DL1 DL1 AR1 ER1 DL0 BL0 BR0,Ha)::
(makeTM BR0 HR1 CR1 DL1 DL1 AR1 ER1 DL0 BL0 CL0,Ha)::
(makeTM BR0 HR1 CR1 EL0 DL1 AR1 EL0 DL0 AR1 CR1,Ha)::
(makeTM BR0 AR0 CL1 AR1 DR1 HR1 EL0 DL1 AR1 CL1,Ha)::
(makeTM BR0 AR0 CL1 DR0 DL0 HR1 EL1 AL0 AR1 BL0,Ha)::
(makeTM BR0 AR0 CL1 EL1 DL0 HR1 EL1 BR0 AR1 CL1,Ha)::
(makeTM BR0 AR0 CR1 AR1 DL0 CL1 AR1 EL1 CR1 HR1,Ha)::
(makeTM BR0 AL1 CL1 DL0 DL1 EL1 AR1 CL1 HR1 AL0,Ha)::
(makeTM BR0 AL1 CR1 DL0 DL1 EL0 AR1 CL1 HR1 AL0,Ha)::
(makeTM BR0 AR1 CL1 ER0 DL0 CL0 AR1 CL1 DL1 HR1,Ha)::
(makeTM BR0 AR1 CL1 ER1 DL0 CL0 AR1 CL1 AL1 HR1,Ha)::
(makeTM BR0 AR1 CL1 ER1 DL1 EL1 AR1 CL1 HR1 AL0,Ha)::
(makeTM BR0 AR1 CL1 ER1 DL1 EL1 AR1 CL1 HR1 BR0,Ha)::
(makeTM BR0 AR1 CL1 ER1 DR1 DL0 AL1 DL1 HR1 CR0,Ha)::
(makeTM BR0 AR1 CR1 DL0 BL1 ER1 BL1 AL1 AR0 HR1,Ha)::
(makeTM BR0 AR1 CR1 DL0 DL1 ER1 BL1 AL1 AR0 HR1,Ha)::
(makeTM BR0 BL0 CL1 DR1 DR1 EL0 AL1 DR0 DR1 HR1,Ha)::
(makeTM BR0 BL0 CL1 DR1 DR1 EL1 AL1 DR0 AR1 HR1,Ha)::
(makeTM BR0 BL0 CL1 DR1 DR1 EL1 AL1 DR0 BL0 HR1,Ha)::
(makeTM BR0 BL0 CL1 ER0 DL0 HR1 AR1 EL0 AR1 AL0,Ha)::
(makeTM BR0 BL0 CL1 ER1 DL0 CL0 ER0 CL1 AR1 HR1,Ha)::
(makeTM BR0 BL0 CR1 BR1 DL1 ER0 BL1 DL1 HR1 AR1,Ha)::
(makeTM BR0 BL0 CR1 ER0 DL1 CL0 AR1 CL0 DR1 HR1,Ha)::
(makeTM BR0 CL0 CR1 DR1 AL1 EL0 ER1 HR1 AL1 AR1,Ha)::
(makeTM BR0 CR0 CL1 DR1 DR1 EL1 AL1 DR0 BL0 HR1,Ha)::
(makeTM BR0 CR1 CL0 ER0 DL1 HR1 ER1 DL0 AR1 EL0,Ha)::
(makeTM BR0 CR1 CR1 BR1 DL1 ER0 BL1 DL1 HR1 AR1,Ha)::
(makeTM BR0 DL0 CR1 HR1 DL1 CR0 EL1 DR0 AL0 BL1,Ha)::
(makeTM BR0 DR0 AL1 CR1 BR1 HR1 AR1 EL1 DL0 AL0,Ha)::
(makeTM BR0 DL1 CL1 BR1 DL1 ER1 AL1 EL1 HR1 CR0,Ha)::
(makeTM BR0 DL1 CR1 BL1 AL1 BR0 AL1 EL0 HR1 BL0,Ha)::
(makeTM BR0 DL1 CR1 CL1 BL1 DR0 AL0 ER1 HR1 AL0,Ha)::
(makeTM BR0 DL1 CR1 ER0 DL1 BR0 AL0 CL1 HR1 CL0,Ha)::
(makeTM BR0 DL1 CR1 ER1 DL1 BR0 AL0 CL1 HR1 AL0,Ha)::
(makeTM BR0 DR1 CL0 AR1 DL1 EL0 AR1 CL0 HR1 DR0,Ha)::
(makeTM BR0 DR1 CL0 AR1 DL1 EL1 AR1 CL0 HR1 BR0,Ha)::
(makeTM BR0 EL1 CL0 AR1 DL1 DR1 CR1 AL0 HR1 BR0,Ha)::
(makeTM BR1 HR1 BL1 CR0 BR0 DL1 EL0 DL1 AL1 DL0,Ha)::
(makeTM BR1 HR1 CL0 BL1 DR1 AL1 ER0 DR0 AL1 DR1,Ha)::
(makeTM BR1 HR1 CL0 BL1 DR1 AL1 ER0 DR0 BR1 DR1,Ha)::
(makeTM BR1 HR1 CR0 BR0 DR1 EL0 ER1 AR0 CL1 BL1,Ha)::
(makeTM BR1 HR1 CR0 ER1 DL1 AR1 EL1 DL0 CR1 ER0,Ha)::
(makeTM BR1 HR1 CL1 BR0 DR0 DL0 EL1 BR1 BR1 AL0,Ha)::
(makeTM BR1 HR1 CL1 BR0 DL1 CR0 EL0 AL1 AR0 CL0,Ha)::
(makeTM BR1 HR1 CL1 CR1 ER0 DL0 CL1 BL0 DR1 AR1,Ha)::
(makeTM BR1 HR1 CR1 DL0 DR1 AR0 BL1 EL1 BL0 ER0,Ha)::
(makeTM BR1 HR1 CR1 EL0 DR0 DL0 ER1 AR0 BL1 EL0,Ha)::
(makeTM BR1 AL0 CL0 CR0 DR1 AL1 AL1 ER0 AL1 HR1,Ha)::
(makeTM BR1 AL0 CL0 CR0 DR1 AL1 AL1 ER1 BL1 HR1,Ha)::
(makeTM BR1 AL0 CL0 CR0 DR1 AL1 AL1 ER1 CR0 HR1,Ha)::
(makeTM BR1 AL0 CL0 DL0 DR1 AL1 AL1 ER1 CR0 HR1,Ha)::
(makeTM BR1 AL0 CR0 DR1 CL1 AL1 AR1 ER1 HR1 BR0,Ha)::
(makeTM BR1 AL0 CR0 DR1 DL0 AR0 EL1 HR1 AR1 EL0,Ha)::
(makeTM BR1 AR0 CL1 AR0 DL0 DR0 AL1 EL0 BL1 HR1,Ha)::
(makeTM BR1 AR0 CL1 BL0 AR1 DL1 EL1 HR1 CL0 BL1,Ha)::
(makeTM BR1 AR0 CL1 CL0 DL0 DR0 AR1 EL1 CL1 HR1,Ha)::
(makeTM BR1 AR0 CL1 CR0 AR1 DL1 EL0 HR1 BL1 ER0,Ha)::
(makeTM BR1 AR0 CL1 DR1 AL1 CL0 ER1 HR1 BR0 AR1,Ha)::
(makeTM BR1 AR0 CL1 EL0 AR1 DL1 EL1 HR1 CL0 CR0,Ha)::
(makeTM BR1 AR0 CL1 EL0 DL0 CL1 AR1 BL1 HR1 DR0,Ha)::
(makeTM BR1 AR0 CL1 EL0 DL0 DR0 AR1 BL1 HR1 DR0,Ha)::
(makeTM BR1 AR0 CR1 BL0 DL1 ER1 AR1 BL1 HR1 DR0,Ha)::
(makeTM BR1 AL1 AL1 CR0 HR1 DR0 DL1 EL1 AL1 AL0,Ha)::
(makeTM BR1 AL1 AL1 CR0 HR1 DR0 DL1 EL1 AR1 AL0,Ha)::
(makeTM BR1 AL1 AL1 CR0 HR1 DR0 DL1 EL1 ER0 AL0,Ha)::
(makeTM BR1 AL1 CL1 AR0 AR0 DL1 CL1 EL0 HR1 AL0,Ha)::
(makeTM BR1 AL1 CL1 AR0 AL1 DL1 CL1 EL0 HR1 AL0,Ha)::
(makeTM BR1 AL1 CL1 AR0 AR1 DL1 CL1 EL0 HR1 AL0,Ha)::
(makeTM BR1 AL1 CL1 AR0 BR1 DL1 CL1 EL0 HR1 AL0,Ha)::
(makeTM BR1 AL1 CL1 CR0 HR1 DR0 DL1 EL1 AL1 AL0,Ha)::
(makeTM BR1 AL1 CL1 CR0 HR1 DR0 DL1 EL1 AR1 AL0,Ha)::
(makeTM BR1 AL1 CR1 EL1 DR1 ER1 AL0 CR1 HR1 BL0,Ha)::
(makeTM BR1 AR1 CL0 CR0 HR1 DR1 EL1 AL0 AL1 EL1,Ha)::
(makeTM BR1 AR1 CL0 CR0 HR1 DR1 EL1 BR1 AL1 EL1,Ha)::
(makeTM BR1 AR1 CR0 ER1 CL1 DR1 AL1 DL0 AR0 HR1,Ha)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 BR0 EL1 HR1 BR0,Ha)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 BR0 EL1 HR1 CL1,Ha)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 CR1 EL1 HR1 BR0,Ha)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL0 CR1 EL1 HR1 CL1,Ha)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 AR1 EL0 HR1 CL1,Ha)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 AR1 EL1 HR1 CL0,Ha)::
(makeTM BR1 AR1 CL1 BL1 AR1 DL1 ER0 EL0 HR1 CL1,Ha)::
(makeTM BR1 AR1 CL1 BL1 CR0 DL1 AR1 EL0 HR1 CL1,Ha)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 HR1 ER1 AR0 AL0,Ha)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 HR1 ER1 AR0 BR1,Ha)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 HR1 ER1 CL1 AL0,Ha)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 HR1 ER1 CL1 BR1,Ha)::
(makeTM BR1 AR1 CL1 DR0 AL1 CL1 HR1 ER1 EL0 BR1,Ha)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 HR1 ER0 CL1 BR1,Ha)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 HR1 ER1 AL1 BR0,Ha)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 HR1 ER1 AR1 BR0,Ha)::
(makeTM BR1 AR1 CL1 DR1 AL1 CL1 HR1 ER1 EL0 BR0,Ha)::
(makeTM BR1 AR1 CR1 EL1 DL1 ER1 AL1 DL1 HR1 CR0,Ha)::
(makeTM BR1 BL0 CL1 BL1 DR0 CR1 AL1 ER1 HR1 AR0,Ha)::
(makeTM BR1 BL0 CL1 DR1 AL1 CL0 ER0 HR1 AR1 EL0,Ha)::
(makeTM BR1 BL0 CL1 ER0 CL0 DL0 ER1 CL1 AR1 HR1,Ha)::
(makeTM BR1 BL0 CR1 BL1 DR0 ER0 DL1 AL1 HR1 DR0,Ha)::
(makeTM BR1 BL0 CR1 BL1 DL1 ER0 DL1 AL1 HR1 DR0,Ha)::
(makeTM BR1 BR0 CL1 BR1 HR1 DL0 ER1 EL0 ER1 AR1,Ha)::
(makeTM BR1 BR0 CR1 BR1 CL1 DL0 ER1 DL1 HR1 AR1,Ha)::
(makeTM BR1 BL1 AL1 CR0 EL0 DR1 HR1 EL0 AR0 CL1,Ha)::
(makeTM BR1 CL0 AL1 BR1 CR1 DR1 AL1 ER1 HR1 BR0,Ha)::
(makeTM BR1 CL0 AL1 BR1 CR1 DR1 BL0 ER1 HR1 BR0,Ha)::
(makeTM BR1 CL0 AL1 DR1 AL1 EL1 ER0 HR1 AR0 ER1,Ha)::
(makeTM BR1 CL0 CR0 HR1 DR1 ER0 EL1 AR0 AL0 EL0,Ha)::
(makeTM BR1 CL0 CR0 BR0 DL1 ER0 EL0 HR1 AL1 BL0,Ha)::
(makeTM BR1 CL0 CL1 EL0 DR1 BL1 AR0 DL1 HR1 DL0,Ha)::
(makeTM BR1 CL0 CL1 ER1 AL1 DL1 AR0 DR1 DR0 HR1,Ha)::
(makeTM BR1 CL0 CR1 DR0 AL1 CL0 DR1 ER1 AR0 HR1,Ha)::
(makeTM BR1 CL0 CR1 DR1 AL1 BR0 ER0 HR1 CL1 AR1,Ha)::
(makeTM BR1 CR0 CL1 DR0 DL0 CL0 ER1 AL0 AR0 HR1,Ha)::
(makeTM BR1 CR0 CL1 ER0 DR1 DL0 AL1 CL1 AR1 HR1,Ha)::
(makeTM BR1 CR0 CL1 ER1 DL0 CR1 AR1 BR0 HR1 AR1,Ha)::
(makeTM BR1 CR0 CR1 ER1 DL1 BR1 AL0 DR1 HR1 DR0,Ha)::
(makeTM BR1 CL1 AL0 DL0 AL1 HR1 BL1 ER1 DR0 BR0,Ha)::
(makeTM BR1 CL1 AL1 DR0 AL1 EL0 BR1 DL1 HR1 DL0,Ha)::
(makeTM BR1 CL1 AL1 ER0 DL0 HR1 BL0 DL1 BR1 DR1,Ha)::
(makeTM BR1 CL1 CL1 DR1 ER1 DL1 CL1 EL0 HR1 AR0,Ha)::
(makeTM BR1 CL1 CL1 ER0 DR1 CL0 AL0 AR0 CL1 HR1,Ha)::
(makeTM BR1 CL1 CL1 ER1 DR1 CL0 AL0 AR0 AR0 HR1,Ha)::
(makeTM BR1 CL1 CL1 ER1 DR1 CL0 AL0 AR0 DL1 HR1,Ha)::
(makeTM BR1 CL1 CL1 ER1 DR1 CL0 AL0 BL0 AR0 HR1,Ha)::
(makeTM BR1 CL1 CR1 BR1 DR1 EL0 AL1 DL1 HR1 AL0,Ha)::
(makeTM BR1 CR1 CR0 EL0 DL1 BR1 AR1 BL1 HR1 DL0,Ha)::
(makeTM BR1 CR1 CL1 CL1 AR1 DR0 EL1 DR1 HR1 BL0,Ha)::
(makeTM BR1 DL0 CL0 BR0 AR1 CL1 EL0 AL1 CL0 HR1,Ha)::
(makeTM BR1 DL0 CR0 CL0 DR1 ER0 AL1 DL0 AR1 HR1,Ha)::
(makeTM BR1 DL0 CL1 BR1 HR1 AL1 EL1 DL1 ER1 BR0,Ha)::
(makeTM BR1 DL0 CL1 DR1 AL1 CL1 HR1 ER1 AR1 BR0,Ha)::
(makeTM BR1 DL0 CL1 ER1 DL0 CL0 ER1 BR1 AR0 HR1,Ha)::
(makeTM BR1 DL0 CR1 ER1 AL1 AL0 HR1 CL1 CR0 EL0,Ha)::
(makeTM BR1 DR0 CL1 BL0 AR1 BL0 DR1 ER1 CR0 HR1,Ha)::
(makeTM BR1 DL1 BL0 CR1 DL1 EL0 ER1 CL1 HR1 AR0,Ha)::
(makeTM BR1 DL1 CR0 BR0 DL0 BR1 EL1 HR1 AL0 AR0,Ha)::
(makeTM BR1 DL1 CR0 EL1 BL1 DR1 CR1 AL0 HR1 BL1,Ha)::
(makeTM BR1 DL1 CL1 BR0 ER0 AR0 EL0 HR1 AL1 BR1,Ha)::
(makeTM BR1 DL1 CL1 DR1 AL1 CL1 BR1 ER0 HR1 CL0,Ha)::
(makeTM BR1 DL1 CR1 BR0 AL1 EL0 CL1 AL0 HR1 BR1,Ha)::
(makeTM BR1 DL1 CR1 BR0 AL1 EL1 CL1 AL0 HR1 DR0,Ha)::
(makeTM BR1 DL1 CR1 BR1 DL1 ER1 AL1 EL1 HR1 CR0,Ha)::
(makeTM BR1 DL1 CR1 EL0 AL1 DR1 ER1 BL0 HR1 AR0,Ha)::
(makeTM BR1 DR1 CL0 DL0 HR1 DL1 AR1 ER0 BL1 ER1,Ha)::
(makeTM BR1 DR1 CR0 HR1 DR1 AL0 EL1 BR1 AL0 EL0,Ha)::
(makeTM BR1 DR1 CR0 CR1 AL1 AL0 CL1 EL1 HR1 DL0,Ha)::
(makeTM BR1 DR1 CL1 AR0 AL1 CL0 HR1 ER0 BL1 CR0,Ha)::
(makeTM BR1 DR1 CL1 AR1 AR1 CL1 HR1 EL0 AR1 DL1,Ha)::
(makeTM BR1 DR1 CL1 CL0 HR1 DR0 AR1 EL0 DL1 CL0,Ha)::
(makeTM BR1 DR1 CL1 EL0 AR0 BL0 ER1 HR1 CL1 CR1,Ha)::
(makeTM BR1 EL0 CR0 HR1 DL1 ER0 AL0 AR0 DL1 DR0,Ha)::
(makeTM BR1 EL0 CR0 BR0 DL1 BR1 AL0 DL1 CR1 HR1,Ha)::
(makeTM BR1 EL0 CR0 BR1 DL1 AR0 AL0 HR1 CR0 CL1,Ha)::
(makeTM BR1 EL0 CL1 BR0 DR0 DL0 AL1 BR1 BR1 HR1,Ha)::
(makeTM BR1 EL0 CL1 CR0 DR1 BR1 AL1 BL0 DL1 HR1,Ha)::
(makeTM BR1 EL0 CR1 AR0 DL1 HR1 EL1 DL1 AL1 CL0,Ha)::
(makeTM BR1 EL0 CR1 ER1 DL1 AR1 HR1 AL1 BR0 DL0,Ha)::
(makeTM BR1 ER0 CL1 AR0 DL0 BL1 AR0 CL1 HR1 BL0,Ha)::
(makeTM BR1 ER0 CL1 AR0 DL1 BL1 ER1 ER0 HR1 BL0,Ha)::
(makeTM BR1 ER0 CL1 AR1 DL1 CL1 BR1 AL1 HR1 CL0,Ha)::
(makeTM BR1 ER0 CL1 AR1 DL1 CL1 DR0 AL1 HR1 CL0,Ha)::
(makeTM BR1 ER0 CL1 BL0 DR1 BL0 AR0 AL0 CR1 HR1,Ha)::
(makeTM BR1 ER0 CR1 AR1 DL0 AL0 HR1 AL1 CL1 ER1,Ha)::
(makeTM BR1 EL1 CR0 BR0 DL1 BR1 AL0 DL1 DR1 HR1,Ha)::
(makeTM BR1 EL1 CL1 HR1 DR0 CR1 EL1 BR1 AL0 EL0,Ha)::
(makeTM BR1 EL1 CL1 BR0 DR0 DL0 AL1 BR1 CR1 HR1,Ha)::
(makeTM BR1 EL1 CL1 BR0 DR0 DL0 AL1 BR1 DL0 HR1,Ha)::
(makeTM BR1 EL1 CL1 CR0 DR1 CR1 AL0 DL1 HR1 BL0,Ha)::
(makeTM BR1 EL1 CL1 ER1 AL1 DR0 HR1 BL0 DL1 CR0,Ha)::
(makeTM BR1 EL1 CR1 ER1 DL1 BR1 AL0 DL1 HR1 AL0,Ha)::
(makeTM BR1 EL1 CR1 ER1 DL1 BR1 AL0 DL1 HR1 DR0,Ha)::
(makeTM BR1 EL1 CR1 ER1 DL1 BR1 AR1 DL1 HR1 AL0,Ha)::
(makeTM BR1 ER1 CL0 AR1 DL1 CL1 AR1 EL1 HR1 DL0,Ha)::
(makeTM BR1 ER1 CL0 BL1 ER1 DL1 BR1 HR1 AR0 ER0,Ha)::
(makeTM BR1 ER1 CL1 AR0 AL1 DL0 EL1 HR1 BL0 EL0,Ha)::
(makeTM BR1 ER1 CL1 AR0 AR1 DL1 EL0 HR1 BL0 EL1,Ha)::
(makeTM BR1 ER1 CL1 AR0 BR1 DL1 EL0 HR1 BL0 EL1,Ha)::
(makeTM BR1 ER1 CL1 AR0 DL0 BL1 AR0 CL1 HR1 DL0,Ha)::
(makeTM BR1 ER1 CR1 AR1 DL1 EL1 BR0 DL1 HR1 CL0,Ha)::
nil.

Definition tm_Lp1 :=
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 DR0 AR1 CL0 AR0,Lp1)::
(makeTM BR1 ER0 CL1 AR0 CL0 DL1 AL1 HR1 BR0 DL0,Lp1)::
nil.

Definition tm_NG_ge8 :=
(makeTM BR0 CR0 CR1 AL0 DL0 AL1 BR1 EL1 DL1 HR1,NG 8 2)::
(makeTM BR0 DL1 AL1 CR1 AL0 EL0 EL1 HR1 BR1 CR0,NG 8 2)::
(makeTM BR0 ER0 CL0 DR1 BR1 AL1 ER1 HR1 CL1 AL0,NG 8 2)::
(makeTM BR1 HR1 CR1 AR0 DL1 DR1 BR0 EL0 EL0 CL0,NG 8 2)::
(makeTM BR1 BL1 CL0 ER0 AL1 DL0 CL1 HR1 ER0 AR0,NG 8 2)::
(makeTM BR1 CL1 AL0 DR1 BR0 ER0 ER1 HR1 AL1 CL0,NG 8 2)::
(makeTM BR1 HR1 CR1 DL0 DL1 AR0 EL1 BL1 CR0 BR0,NG 9 2)::
(makeTM BR1 ER1 CL0 EL0 AR1 DL0 EL1 HR1 CL1 AR0,NG 9 2)::
(makeTM BR0 CL0 CL1 AL0 BR1 DR0 AL1 ER1 DR1 HR1,NG 10 2)::
(makeTM BR0 DL1 CR1 EL0 AL0 EL1 AL1 HR1 BR1 CR0,NG 10 2)::
(makeTM BR0 ER1 CL0 DR1 AL1 ER0 BR1 HR1 CL1 AL0,NG 10 2)::
(makeTM BR1 HR1 CR1 AR0 DL1 DR1 BR0 EL0 CL1 CL0,NG 10 3)::
(makeTM BR1 AL0 CR0 HR1 DR1 AL0 EL1 ER0 AR1 CL0,NG 10 9)::
(makeTM BR1 BL0 CL1 ER0 DL1 CR0 EL0 HR1 AL1 CR0,NG 10 9)::
(makeTM BR1 BL1 CL0 ER0 AL1 DL0 CL1 HR1 AR1 AR0,NG 10 3)::
(makeTM BR1 CR0 AL1 DL0 AL0 BR0 CR1 EL1 DL1 HR1,NG 10 2)::
(makeTM BR1 CR0 AL1 EL0 EL1 DR1 CR1 HR1 BR0 AL0,NG 10 2)::
(makeTM BR1 EL0 CL0 EL1 AR0 DL1 CL1 HR1 AR1 BR0,NG 10 2)::
(makeTM BR1 ER0 CL1 AL0 ER1 DL0 CL0 HR1 BR0 AL1,NG 10 2)::
(makeTM BR1 EL1 CL0 DR0 DR1 BR0 CL1 AL0 AL1 HR1,NG 10 2)::
nil.

Definition tm_NG_LRU :=
(makeTM BR0 HR1 CL0 BR1 DL1 CL1 ER1 AL1 AL0 ER0,NG_LRU 2)::
(makeTM BR0 HR1 CL0 BR1 DL1 CL1 ER1 AL1 CL0 ER0,NG_LRU 2)::
(makeTM BR0 HR1 CL1 AR0 DL0 CL0 ER1 CL1 ER1 AR1,NG_LRU 2)::
(makeTM BR0 HR1 CL1 AR1 DL0 CL0 AR0 ER1 ER1 CL1,NG_LRU 2)::
(makeTM BR0 HR1 CR1 AR0 DL1 BR1 CR0 EL0 CL0 DL0,NG_LRU 4)::
(makeTM BR0 HR1 CR1 BR1 DL1 DL0 EL0 ER0 AL1 CL1,NG_LRU 2)::
(makeTM BR0 AL0 AL1 CL0 DR0 CL1 ER1 DR1 BR1 HR1,NG_LRU 2)::
(makeTM BR0 AL0 AL1 CL1 DR0 CL0 DR1 ER1 BR1 HR1,NG_LRU 2)::
(makeTM BR0 AL0 AL1 CL1 DR0 CL1 ER1 DR1 BR1 HR1,NG_LRU 2)::
(makeTM BR0 AL0 AL1 CR1 DL0 HR1 ER0 DL1 BR1 ER1,NG_LRU 2)::
(makeTM BR0 AL0 AL1 CR1 DL1 HR1 ER0 DL0 ER1 BR1,NG_LRU 2)::
(makeTM BR0 AL0 AL1 CR1 DL1 HR1 ER0 DL1 BR1 ER1,NG_LRU 2)::
(makeTM BR0 AL0 CL0 HR1 DR0 CL1 ER1 DR1 AL1 BR1,NG_LRU 2)::
(makeTM BR0 AL0 CL0 DR0 AL1 CL1 ER1 DR1 CR1 HR1,NG_LRU 2)::
(makeTM BR0 AL0 CR0 BR1 DR1 HR1 EL0 DR1 AL1 EL1,NG_LRU 2)::
(makeTM BR0 AL0 CL1 HR1 DR0 CL0 DR1 ER1 AL1 BR1,NG_LRU 2)::
(makeTM BR0 AL0 CL1 HR1 DR0 CL1 ER1 DR1 AL1 BR1,NG_LRU 2)::
(makeTM BR0 AL0 CL1 DR0 AL1 CL1 ER1 DR1 CR1 HR1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 HR1 AL1 DL0 ER0 DL1 BR1 ER1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 HR1 AL1 DL1 ER0 DL0 ER1 BR1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 HR1 AL1 DL1 ER0 DL1 BR1 ER1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 AR0 DR1 CR1 ER1 HR1 AL1 EL1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 BR1 AL1 DR1 EL0 HR1 BR0 EL1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 BR1 AL1 DR1 EL1 HR1 BR0 EL1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 BR1 DR0 HR1 EL0 DR0 EL1 AL1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 BR1 DR1 HR1 AL1 EL0 BR0 EL1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 BR1 DR1 HR1 AL1 EL0 DR0 EL1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 BR1 DR1 HR1 AL1 EL1 BR0 EL1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 CR0 DR1 CR1 ER1 HR1 AL1 EL1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 DR0 AL1 CL1 HR1 ER1 BR1 ER1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 DR0 AL1 CL1 ER1 DR1 BR1 HR1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 DR0 AL1 CL1 ER1 DR1 CR1 HR1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 ER0 DR1 HR1 AL1 DL1 BR1 ER1,NG_LRU 2)::
(makeTM BR0 AL0 CR1 ER0 DR1 HR1 AL1 DL1 CR1 ER1,NG_LRU 2)::
(makeTM BR0 AR0 CL0 EL0 BR1 DL1 CL1 HR1 EL1 AR1,NG_LRU 2)::
(makeTM BR0 AR0 CL0 EL0 DL1 HR1 BR1 CL1 EL1 AR1,NG_LRU 2)::
(makeTM BR0 AR0 CL0 EL1 BR1 DL0 CL1 HR1 EL1 AR1,NG_LRU 2)::
(makeTM BR0 AR0 CL0 EL1 DL0 HR1 AR1 CL1 EL1 AR1,NG_LRU 2)::
(makeTM BR0 AL1 CL0 BR1 DR0 AL0 CL1 ER1 DR1 HR1,NG_LRU 2)::
(makeTM BR0 AL1 CL0 BR1 DR0 AL0 ER1 HR1 CL1 DR1,NG_LRU 2)::
(makeTM BR0 AL1 CL0 ER0 BR1 DL1 CL1 HR1 AL0 ER1,NG_LRU 2)::
(makeTM BR0 AL1 CL0 ER0 DL1 HR1 BR1 CL1 AL0 ER1,NG_LRU 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 AL1 HR1 EL0 BR0 DL0,NG_LRU 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 ER1 BR0 DL0 AL0 HR1,NG_LRU 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 ER1 BR0 DL0 AL1 HR1,NG_LRU 2)::
(makeTM BR0 AL1 CR1 BR1 DL1 ER1 ER0 DL0 AL0 HR1,NG_LRU 2)::
(makeTM BR0 AL1 CR1 BR1 DR1 HR1 EL1 AL0 BR0 EL0,NG_LRU 2)::
(makeTM BR0 AL1 CR1 BR1 DR1 HR1 EL1 AL0 DR0 EL0,NG_LRU 2)::
(makeTM BR0 AL1 CR1 BR1 DR1 HR1 EL1 AL1 BR0 EL0,NG_LRU 2)::
(makeTM BR0 AL1 CR1 BR1 DR1 HR1 EL1 AL1 CR0 EL0,NG_LRU 2)::
(makeTM BR0 AR1 CR1 HR1 DL0 CR1 EL1 DL1 AR0 EL0,NG_LRU 2)::
(makeTM BR0 BL0 CR1 ER1 DL0 HR1 EL1 DL1 AR1 AR0,NG_LRU 2)::
(makeTM BR0 CL0 CL1 BR1 DL1 AL1 ER1 DR1 HR1 CR1,NG_LRU 3)::
(makeTM BR0 CR0 AL1 CR1 DL0 AL0 BR1 EL1 DL1 HR1,NG_LRU 2)::
(makeTM BR0 CL1 CL1 HR1 DL1 ER0 EL0 DL0 ER1 AR1,NG_LRU 2)::
(makeTM BR0 DL0 AL1 CR1 BR1 HR1 ER0 DL1 AL0 ER1,NG_LRU 2)::
(makeTM BR0 DL0 CR1 HR1 AL1 BR1 ER0 DL1 AL0 ER1,NG_LRU 2)::
(makeTM BR0 DL0 CR1 BR1 AL0 CR0 EL1 DL1 BL1 HR1,NG_LRU 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 CL1 ER0 AL0 HR1 BR0,NG_LRU 2)::
(makeTM BR0 DL0 CR1 BR1 DL1 EL1 HR1 AL0 BR0 EL1,NG_LRU 2)::
(makeTM BR0 DR0 AL1 CR1 BR1 HR1 DR0 EL1 EL0 AL0,NG_LRU 2)::
(makeTM BR0 DR0 AL1 CR1 BR1 HR1 DR1 EL1 AL0 EL0,NG_LRU 2)::
(makeTM BR0 DR0 CL0 AL0 DR1 EL1 AL1 BR1 CL1 HR1,NG_LRU 2)::
(makeTM BR0 DR0 CL1 ER1 DR1 AL1 AL0 CL0 BR1 HR1,NG_LRU 2)::
(makeTM BR0 DR0 CL1 ER1 DR1 AL1 CL0 AL0 BR1 HR1,NG_LRU 2)::
(makeTM BR0 DR0 CR1 HR1 AL1 BR1 DR1 EL1 AL0 EL0,NG_LRU 2)::
(makeTM BR0 DL1 AL1 CR1 BR1 HR1 ER0 DL0 ER1 AL0,NG_LRU 2)::
(makeTM BR0 DL1 CR1 HR1 AL1 BR1 ER0 DL0 ER1 AL0,NG_LRU 2)::
(makeTM BR0 DR1 AL1 CR0 BR1 HR1 DR1 EL1 AL0 EL0,NG_LRU 2)::
(makeTM BR0 DR1 AL1 CR1 BR1 HR1 DR0 EL1 EL0 AL0,NG_LRU 2)::
(makeTM BR0 DR1 CR1 HR1 AL1 BR1 DR0 EL1 EL0 AL0,NG_LRU 2)::
(makeTM BR0 EL0 AL1 CL1 DR0 CL1 BR1 DR1 HR1 AL0,NG_LRU 2)::
(makeTM BR0 EL0 CR0 AR1 DR1 BR0 EL1 HR1 AL0 DL1,NG_LRU 2)::
(makeTM BR0 EL0 CL1 DR0 AL1 CL1 CR1 DR1 HR1 AL0,NG_LRU 2)::
(makeTM BR0 EL0 CR1 CR0 DR1 CR1 AL1 DL1 HR1 AL0,NG_LRU 2)::
(makeTM BR0 EL0 CR1 ER0 DR1 CR1 AL1 DL1 HR1 AL0,NG_LRU 2)::
(makeTM BR0 ER0 CR1 HR1 DL1 BR1 DL0 AL0 ER0 DL1,NG_LRU 2)::
(makeTM BR0 EL1 CR1 HR1 DL1 BR1 DR1 AL0 DR0 EL0,NG_LRU 2)::
(makeTM BR0 ER1 CL0 AR0 DL0 BL1 EL1 CL0 AR1 HR1,NG_LRU 2)::
(makeTM BR0 ER1 CR0 HR1 DL1 BR1 AL0 DL0 ER1 DL1,NG_LRU 2)::
(makeTM BR0 ER1 CR1 HR1 DL1 BR1 DL0 AL0 ER0 DL1,NG_LRU 2)::
(makeTM BR0 ER1 CR1 AR0 DL1 HR1 EL0 CL1 AR0 DL0,NG_LRU 2)::
(makeTM BR1 HR1 BL1 CR1 ER0 DL1 AL1 DL0 BR0 ER0,NG_LRU 2)::
(makeTM BR1 HR1 CL0 BR0 CL1 DL1 ER1 AL1 AL0 ER0,NG_LRU 2)::
(makeTM BR1 HR1 CL0 BR1 DL1 CL1 ER0 DL0 AR0 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CL0 BR1 DL1 CL1 ER1 AL1 AL0 ER0,NG_LRU 2)::
(makeTM BR1 HR1 CR0 AR1 DL0 BR0 EL0 CL1 AL1 DL0,NG_LRU 2)::
(makeTM BR1 HR1 CR0 BR1 DR0 CR0 DL1 EL0 AL1 EL0,NG_LRU 2)::
(makeTM BR1 HR1 CL1 AR0 BR0 DR1 DR1 EL1 CL0 EL0,NG_LRU 2)::
(makeTM BR1 HR1 CL1 AR1 AR0 DL0 ER0 DL1 CL0 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 AR1 AR0 DR0 DR1 EL1 CL0 EL0,NG_LRU 2)::
(makeTM BR1 HR1 CL1 AR1 AR0 DL1 ER0 DL0 ER1 CL0,NG_LRU 2)::
(makeTM BR1 HR1 CL1 AR1 AR0 DR1 DR0 EL1 EL0 CL0,NG_LRU 2)::
(makeTM BR1 HR1 CL1 AR1 CL0 DL0 AR0 ER0 ER0 CL1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 AR1 CL0 DL0 AR0 ER1 ER0 CL1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 AR1 CR1 DL0 AR0 EL1 CR0 EL0,NG_LRU 2)::
(makeTM BR1 HR1 CL1 BL1 DR0 CL0 BL1 ER0 AR1 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 BL1 DR0 CL0 BR1 ER0 AR1 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 BL1 DR0 CL0 ER1 CR0 AR1 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 BL1 DR0 CL0 ER1 DR1 AR1 DR0,NG_LRU 2)::
(makeTM BR1 HR1 CL1 BL1 DR0 CL0 ER1 ER0 AR1 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 DL0 AR0 CL0 ER0 DL1 AR1 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 DL0 ER1 DL0 CL0 BR0 DR0 AR0,NG_LRU 6)::
(makeTM BR1 HR1 CL1 DL1 AR0 CL0 ER0 DL0 ER1 AR1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 DL1 AR0 CL0 ER0 DL1 AR1 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CL1 DL1 BR0 CL0 ER0 DL1 AR1 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CR1 DL0 DR0 CR0 DL1 EL1 AL0 BR1,NG_LRU 2)::
(makeTM BR1 HR1 CR1 ER0 DL1 CL1 BR0 DL0 AR1 ER1,NG_LRU 2)::
(makeTM BR1 HR1 CR1 ER0 DL1 CL1 ER0 DL0 AR1 ER1,NG_LRU 2)::
(makeTM BR1 AR0 BL1 CL1 DL0 HR1 EL0 DL0 ER1 AR0,NG_LRU 2)::
(makeTM BR1 AR0 CL1 HR1 CR1 DL1 EL0 AR1 CL0 EL0,NG_LRU 2)::
(makeTM BR1 AR0 CL1 HR1 DL0 CL1 EL0 DL0 ER1 AR0,NG_LRU 2)::
(makeTM BR1 AL1 CR1 ER1 DL1 CL1 HR1 BL1 AL0 BR0,NG_LRU 3)::
(makeTM BR1 AR1 CL0 BR0 AR0 DL0 EL1 DL1 AL1 HR1,NG_LRU 2)::
(makeTM BR1 AR1 CL0 BR0 AL1 DL0 EL1 DL1 AL1 HR1,NG_LRU 2)::
(makeTM BR1 AR1 CL0 BR0 DL1 BL0 EL1 DL1 AL1 HR1,NG_LRU 2)::
(makeTM BR1 AR1 CL0 BR0 EL1 DL0 CL1 DL1 AL1 HR1,NG_LRU 2)::
(makeTM BR1 AR1 CL0 BR0 EL1 DL0 EL1 DL1 AL1 HR1,NG_LRU 2)::
(makeTM BR1 AR1 CL0 ER0 HR1 DL0 AL1 DL1 BR1 BR0,NG_LRU 2)::
(makeTM BR1 AR1 CL0 ER0 HR1 DL0 AL1 DL1 DL0 BR0,NG_LRU 2)::
(makeTM BR1 AR1 CR0 HR1 DL0 CR0 DL1 EL1 AR0 EL0,NG_LRU 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL0 AR0 CL0 HR1 AR0,NG_LRU 2)::
(makeTM BR1 AR1 CL1 BL1 ER0 DL0 CL1 CL0 HR1 AR0,NG_LRU 2)::
(makeTM BR1 AR1 CL1 CL0 DL0 DR0 EL1 BL1 AR0 HR1,NG_LRU 2)::
(makeTM BR1 AR1 CL1 DR1 AR0 CL0 EL0 HR1 AR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CL1 DR1 AR0 CL0 EL1 HR1 AR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CL1 DR1 DR0 CL0 EL0 HR1 AR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CL1 EL1 HR1 DL0 AR0 CL0 AR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CR1 HR1 DL1 CL1 ER0 DL0 BR1 AR0,NG_LRU 2)::
(makeTM BR1 AR1 CR1 HR1 DL1 CL1 ER0 DL0 CL0 AR0,NG_LRU 2)::
(makeTM BR1 AR1 CR1 HR1 DL1 CL1 ER0 DL0 CR1 AR0,NG_LRU 2)::
(makeTM BR1 AR1 CR1 HR1 DL1 EL0 AR0 DL0 AR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CR1 HR1 DL1 EL0 AR0 DL0 CR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CR1 HR1 DL1 EL0 CR0 DL0 AR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CR1 HR1 DL1 EL1 AR0 DL0 AR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CR1 HR1 DL1 EL1 BR0 DL0 AR0 EL1,NG_LRU 2)::
(makeTM BR1 AR1 CR1 AR0 DR1 HR1 EL1 DL1 BR0 EL0,NG_LRU 2)::
(makeTM BR1 AR1 CR1 ER0 DL1 CL1 BR0 DL0 HR1 AR1,NG_LRU 2)::
(makeTM BR1 BR0 CL0 AR0 HR1 DL0 EL1 DL1 BR1 ER1,NG_LRU 2)::
(makeTM BR1 BR0 CR0 CL0 DR1 AR1 EL0 HR1 AL1 EL1,NG_LRU 2)::
(makeTM BR1 BR0 CL1 AR0 HR1 DL1 EL0 DL0 ER1 BR1,NG_LRU 2)::
(makeTM BR1 BR0 CR1 BR1 DL1 CL1 AR0 EL0 HR1 DL0,NG_LRU 2)::
(makeTM BR1 BR0 CR1 BR1 DR1 HR1 EL1 DL1 AR0 EL0,NG_LRU 2)::
(makeTM BR1 CL0 AL0 DL1 AL1 HR1 DL1 ER1 BR0 ER0,NG_LRU 2)::
(makeTM BR1 CL0 CR0 BR0 CL1 DL1 EL0 AR1 AR1 HR1,NG_LRU 2)::
(makeTM BR1 CR0 AL0 BR0 DL0 CR1 EL1 DL1 AL1 HR1,NG_LRU 2)::
(makeTM BR1 CL1 AL0 BR0 DR0 HR1 EL0 DR1 AL1 EL1,NG_LRU 2)::
(makeTM BR1 CL1 AL0 BR0 DR1 HR1 EL0 DR0 EL1 AL1,NG_LRU 2)::
(makeTM BR1 CL1 AL0 BR0 DR1 HR1 EL0 DR1 AL1 EL1,NG_LRU 2)::
(makeTM BR1 CL1 AL0 CL0 DR0 BR0 AL1 ER1 DR1 HR1,NG_LRU 2)::
(makeTM BR1 CL1 AL0 DL0 AL1 HR1 DL0 ER1 ER0 BR0,NG_LRU 2)::
(makeTM BR1 CL1 AL0 DL0 AL1 HR1 DL1 ER1 BR0 ER0,NG_LRU 2)::
(makeTM BR1 CL1 AL0 DR0 AL1 HR1 EL0 DR1 BR0 EL1,NG_LRU 2)::
(makeTM BR1 CL1 AL0 DL1 AL1 HR1 DL0 ER1 ER0 BR0,NG_LRU 2)::
(makeTM BR1 CL1 AL0 DR1 AL1 HR1 EL0 DR0 EL1 BR0,NG_LRU 2)::
(makeTM BR1 CL1 CL0 AL0 DR0 BR0 AL1 ER1 DR1 HR1,NG_LRU 2)::
(makeTM BR1 CL1 CL0 BR0 DL1 AL1 AR1 ER1 HR1 DR1,NG_LRU 2)::
(makeTM BR1 CR1 AL0 BR0 DL0 CR0 DL1 EL1 AL1 HR1,NG_LRU 2)::
(makeTM BR1 CR1 AL0 BR0 DL0 CR1 EL1 DL1 AL1 HR1,NG_LRU 2)::
(makeTM BR1 CR1 AL0 ER0 DL0 CR1 AL1 DL1 HR1 BR0,NG_LRU 2)::
(makeTM BR1 DL0 CR1 BR1 AL0 CR0 EL1 DL1 BL1 HR1,NG_LRU 2)::
(makeTM BR1 DL0 CR1 BR1 AL0 ER0 BL1 DL1 HR1 CR0,NG_LRU 2)::
(makeTM BR1 DR0 CL0 BL0 CR1 DR1 EL1 AR0 HR1 BL1,NG_LRU 2)::
(makeTM BR1 DR0 CL1 BL1 AR0 CL0 HR1 ER1 AR1 ER1,NG_LRU 2)::
(makeTM BR1 DR0 CL1 BL1 AR0 CL0 ER1 DR1 AR1 HR1,NG_LRU 2)::
(makeTM BR1 DR0 CL1 BL1 AR0 CL0 ER1 DR1 BR1 HR1,NG_LRU 2)::
(makeTM BR1 DR0 CL1 BL1 AR1 BL0 ER0 AR1 HR1 BL1,NG_LRU 5)::
(makeTM BR1 DL1 CR0 BR0 DL0 EL1 AL0 HR1 EL1 BR1,NG_LRU 2)::
(makeTM BR1 DR1 CL0 HR1 DL1 CL1 ER1 ER0 AR0 AL0,NG_LRU 2)::
(makeTM BR1 EL0 CR0 BR0 DL1 BR1 DL1 EL1 AL0 HR1,NG_LRU 2)::
(makeTM BR1 ER0 CL1 HR1 DL0 BL1 ER0 CL0 AR0 DR1,NG_LRU 3)::
(makeTM BR1 ER0 CL1 AR1 BR0 DL0 BL0 CL0 AR0 HR1,NG_LRU 3)::
(makeTM BR1 ER0 CL1 BL1 DR0 CL0 AR1 HR1 DR1 ER1,NG_LRU 2)::
(makeTM BR1 ER0 CL1 ER0 EL0 DL0 AL1 HR1 BR0 AL0,NG_LRU 6)::
(makeTM BR1 ER0 CR1 HR1 DL1 CL1 AR0 DL0 AR1 ER1,NG_LRU 2)::
(makeTM BR1 ER0 CR1 HR1 DL1 CL1 AR0 DL0 BR1 ER1,NG_LRU 2)::
(makeTM BR1 ER0 CR1 BR1 DL1 CL1 AR0 EL0 HR1 DL0,NG_LRU 2)::
(makeTM BR1 ER0 CR1 BR1 DR1 HR1 EL1 DL1 AR0 EL0,NG_LRU 2)::
(makeTM BR1 EL1 BL1 CR0 EL0 DR1 BL0 DR0 AL1 HR1,NG_LRU 2)::
(makeTM BR1 EL1 CL1 DR1 BR0 DR0 AL0 CL0 AL1 HR1,NG_LRU 2)::
(makeTM BR1 EL1 CL1 DR1 DR0 BR0 AL0 CL0 AL1 HR1,NG_LRU 2)::
(makeTM BR1 ER1 CL0 BR0 DL1 CL1 AL1 HR1 CL0 ER1,NG_LRU 2)::
nil.

Definition tm_NG0' :=
(makeTM BR1 AL0 CR0 HR1 DR1 DR0 EL1 ER0 AR1 CL0,NG 0 17)::
(makeTM BR1 BL0 CL1 ER0 DL1 CR0 EL0 HR1 AL1 AL0,NG 0 17)::
(makeTM BR1 DL0 CR1 BL0 DR0 HR1 ER1 BL0 AL1 AR0,NG 0 21)::
(makeTM BR1 DL0 CR1 BL0 DR0 HR1 ER1 ER0 AL1 AR0,NG 0 20)::
nil.

Definition tm_RWL' :=
(makeTM BR1 HR1 CR0 DR1 DL0 CR1 EL1 AR0 AR1 EL0,RWL 20 2)::
nil.


Definition DFA_from_list(ls:list(nat*nat))(x:nat)(i:Σ) :=
  let (a,b) := nth x ls (0,0) in
  match i with
  | Σ0 => a
  | Σ1 => b
  end.



Definition tm_DNV :=
(makeTM BR1 AR0 CL1 HR1 DL0 CL0 ER0 AR1 ER1 DL1,
DNV 2 (DFA_from_list ((0,1)::(2,0)::(2,2)::nil)))::

(makeTM BR1 CL1 AL1 BR1 DL1 AL0 ER1 DR0 HR1 BR0,
DNV 12 (DFA_from_list ((0,1)::(2,3)::(4,5)::(4,6)::(4,4)::(4,7)::(4,8)::(4,9)::(4,10)::(4,11)::(4,3)::(4,12)::(4,7)::nil)))::

(makeTM BR1 AL1 AL1 CR1 HR1 DR0 AL0 ER0 DL0 ER1,
DNV 3 (DFA_from_list ((0,1)::(2,3)::(2,2)::(0,1)::nil)))::

(makeTM BR1 HR1 CR0 BR0 CL1 DL0 AR1 EL0 AL0 EL0,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,4)::(5,6)::(4,4)::(7,4)::(8,4)::(9,10)::(4,4)::(5,6)::(4,3)::nil)))::

(makeTM BR1 AR1 CL1 DL0 HR1 DL1 ER1 EL1 AR0 BL0,
DNV 9 (DFA_from_list ((0,1)::(2,3)::(4,5)::(6,0)::(4,4)::(4,7)::(4,8)::(4,2)::(4,9)::(4,6)::nil)))::

(makeTM BR1 BL1 CR0 DL0 DR1 CR1 EL1 AL0 HR1 AL1,
DNV 9 (DFA_from_list ((0,1)::(2,3)::(4,5)::(6,0)::(4,4)::(4,7)::(4,8)::(4,2)::(4,9)::(4,6)::nil)))::

(makeTM BR1 AL1 CR1 DR1 AL0 ER0 HR1 CR0 CL0 ER1,
DNV 3 (DFA_from_list ((0,1)::(2,3)::(2,2)::(0,1)::nil)))::

(makeTM BR1 AR1 CL1 CL0 EL0 DR0 AR0 BL1 DL1 HR1,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(5,5)::(6,7)::(5,5)::(5,5)::(8,9)::(5,5)::(10,4)::(4,5)::nil)))::

(makeTM BR1 HR1 CR0 BR0 DL0 AL1 DL1 EL1 AL0 EL0,
DNV 3 (DFA_from_list ((0,1)::(2,1)::(1,3)::(3,3)::nil)))::

(makeTM BR1 DR0 CR1 HR1 DL1 EL1 ER1 DL1 AR1 CL0,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(6,7)::(8,8)::(9,6)::(9,6)::(4,10)::(9,9)::(8,8)::nil)))::

(makeTM BR1 AR0 CL1 HR1 DL0 CL0 ER0 AR1 ER1 AR0,
DNV 2 (DFA_from_list ((0,1)::(2,0)::(2,2)::nil)))::

(makeTM BR1 HR1 CL0 DR1 DL1 CL1 ER1 ER0 AR0 BL0,
DNV 11 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(6,7)::(6,8)::(6,6)::(6,8)::(9,10)::(4,6)::(11,7)::(6,5)::nil)))::

(makeTM BR1 BR0 CR0 DL0 DR1 HR1 EL0 AR1 AL1 EL1,
DNV 10 (DFA_from_list ((0,1)::(2,1)::(3,4)::(5,6)::(5,7)::(5,5)::(5,7)::(8,9)::(3,5)::(10,6)::(5,4)::nil)))::

(makeTM BR1 HR1 CR0 BR0 DL0 EL1 DL1 EL0 AL1 CR1,
DNV 3 (DFA_from_list ((0,1)::(2,1)::(1,3)::(3,3)::nil)))::

(makeTM BR1 CR1 CL1 BR1 DL1 AR0 EL1 BL0 AL1 HR1,
DNV 8 (DFA_from_list ((0,1)::(2,1)::(3,4)::(5,6)::(7,2)::(5,5)::(5,5)::(3,8)::(7,2)::nil)))::

(makeTM BR1 DL1 CL1 HR1 DL0 CL0 ER0 AR1 ER1 AR0,
DNV 2 (DFA_from_list ((0,1)::(2,0)::(2,2)::nil)))::

(makeTM BR1 AL1 CR1 EL0 DR1 AR0 ER1 HR1 AL1 BL1,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(4,4)::(4,6)::(7,8)::(4,9)::(6,6)::(4,10)::(4,10)::nil)))::

(makeTM BR1 HR1 CR0 BR0 DL0 EL1 DL1 EL0 AL1 EL0,
DNV 3 (DFA_from_list ((0,1)::(2,1)::(1,3)::(3,3)::nil)))::

(makeTM BR1 EL0 CR1 HR1 DR0 CR0 DL1 AL0 BL0 EL0,
DNV 9 (DFA_from_list ((0,1)::(2,3)::(4,4)::(5,6)::(4,4)::(7,4)::(2,4)::(8,9)::(5,6)::(4,3)::nil)))::

(makeTM BR1 AR0 CL1 HR1 CL0 DL0 ER1 BR0 ER0 AR1,
DNV 3 (DFA_from_list ((0,1)::(2,3)::(1,0)::(3,3)::nil)))::

(makeTM BR1 HR1 CL1 DL1 DR1 CL1 ER1 BL0 AR1 CR0,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(6,4)::(6,7)::(6,6)::(8,9)::(6,10)::(7,7)::(6,4)::nil)))::

(makeTM BR1 HR1 CR0 BR0 DL0 EL1 DL1 CR1 AL1 EL0,
DNV 3 (DFA_from_list ((0,1)::(2,1)::(1,3)::(3,3)::nil)))::

(makeTM BR1 DL0 CR1 ER0 DR1 HR1 EL1 AL1 AR1 EL1,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(4,4)::(4,6)::(7,8)::(4,9)::(6,6)::(4,10)::(4,10)::nil)))::

nil.


Notation "( a , b ; c , d )" := (a%nat,b%Z,c%nat,d%Z).

Definition tm_WA :=

(makeTM BR1 HR1 CR0 CL1 DR1 CR1 EL1 DL1 AR0 EL0,
WA 2
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;2,0)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(0,-1;2,0)::nil)))::

(makeTM BR1 HR1 CR0 BL1 DR1 CR1 EL1 DL1 AR0 EL0,
WA 2
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;2,0)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(0,-1;2,0)::nil)))::

(makeTM BR1 HR1 CR0 CR1 DR1 CR1 EL1 DL1 AR0 EL0,
WA 2
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;2,0)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,-1)::(1,0;1,0)::(0,0;2,0)::nil)))::

(makeTM BR1 HR1 CR0 CR1 DR1 BR1 EL1 DL1 AR0 EL0,
WA 2
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;2,0)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,-1)::(1,0;1,0)::(0,0;2,0)::nil)))::

(makeTM BR1 AR1 CL1 BL1 DR0 CL0 ER1 HR1 AR0 AR1,
WA 3
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;2,0)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(0,-1;2,0)::nil)))::

(makeTM BR1 AR1 CL1 BL1 DR0 CL0 ER1 HR1 AR0 AL1,
WA 3
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;2,0)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(0,-1;2,0)::nil)))::

(makeTM BR1 AR1 CL1 BL1 DR0 CL0 ER1 HR1 AR0 EL1,
WA 3
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,0;2,0)::(1,0;2,1)::nil))
2 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(0,-1;2,0)::nil)))::

(makeTM BR1 ER1 CL1 BL1 DR0 CL0 ER1 HR1 AR0 AR1,
WA 3
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;2,0)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(0,-1;2,0)::nil)))::

(makeTM BR1 AR1 CL1 EL1 DR0 CL0 ER1 HR1 AR0 BL1,
WA 3
4 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;4,0)::(1,0;2,0)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(0,-1;2,0)::nil)))::

(makeTM BR1 HR1 CR0 DL1 DR1 CR1 EL1 BL1 AR0 EL0,
WA 2
4 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,0;4,0)::(1,0;2,1)::(1,0;2,0)::nil))
2 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(0,-1;2,0)::nil)))::

(makeTM BR1 ER1 CL1 BL1 DR0 CL0 EL1 HR1 AR0 AR1,
WA 2
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,1;3,0)::(1,0;2,0)::nil))
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,0;2,0)::(2,0;2,-1)::nil)))::

(makeTM BR1 HR1 CL0 CL1 DL1 BL1 ER1 DR1 AL0 ER0,
WA 2
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,0;2,0)::(2,0;2,1)::nil))
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,-1;3,0)::(1,0;2,0)::nil)))::

(makeTM BR1 CL1 CL1 AR1 EL0 DL0 AR0 DR1 HR1 CL0,
WA 2
4 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(4,0;3,0)::(4,1;2,0)::(1,0;2,0)::nil))
3 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,0;2,-1)::(2,0;2,0)::nil)))::

(makeTM BR1 CL1 BL1 AR1 EL0 DL0 AR0 DR1 HR1 CL0,
WA 2
7 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,0;4,0)::(1,0;7,0)::(5,1;6,0)::(1,0;7,0)::(3,0;4,0)::(3,0;4,0)::nil))
6 (WDFA_from_list ((0,0;2,0)::(1,0;1,0)::(3,0;4,-1)::(5,0;6,0)::(3,0;4,-1)::(3,0;4,-1)::(3,0;4,-1)::nil)))::

(makeTM BR1 CR0 CL1 EL0 DL0 BL0 AR1 HR1 BL1 DR0,
WA 1
57 (WDFA_from_list ((0,0;1,0)::(2,0;3,0)::(4,0;5,0)::(6,0;6,0)::(7,0;8,0)::(9,0;10,0)::(6,0;6,0)::(11,0;12,0)::(13,0;14,0)::(6,0;15,0)::(16,0;17,0)::(4,-1;18,0)::(19,0;20,0)::(6,0;6,0)::(21,0;22,0)::(23,0;24,0)::(6,0;25,0)::(6,0;6,0)::(26,0;27,0)::(6,0;6,0)::(28,0;29,0)::(6,0;30,0)::(6,0;6,0)::(6,0;1,0)::(6,0;6,0)::(31,0;32,0)::(6,0;33,0)::(34,0;35,0)::(6,0;36,0)::(6,0;6,0)::(37,0;38,0)::(6,0;39,0)::(6,0;6,0)::(40,0;41,0)::(6,-2;42,0)::(6,0;6,0)::(43,0;44,0)::(6,0;45,0)::(6,0;6,0)::(46,0;47,0)::(6,0;7,0)::(6,0;6,0)::(48,0;49,0)::(6,0;50,0)::(6,0;6,0)::(8,0;51,0)::(6,0;52,0)::(6,0;6,0)::(6,-2;53,0)::(6,0;6,0)::(12,0;54,0)::(6,0;6,0)::(16,0;17,0)::(55,0;56,0)::(6,0;6,0)::(6,-2;57,0)::(6,0;6,0)::(34,0;35,0)::nil))
36 (WDFA_from_list ((0,0;1,0)::(2,0;3,0)::(4,0;5,0)::(6,0;7,1)::(8,0;9,0)::(10,0;11,0)::(12,0;11,0)::(13,0;1,0)::(11,0;11,0)::(14,0;11,0)::(15,0;16,0)::(11,0;11,0)::(17,0;18,0)::(19,0;11,0)::(20,0;21,0)::(11,0;11,0)::(7,0;11,0)::(11,0;11,0)::(22,0;11,0)::(23,0;24,0)::(11,0;11,0)::(25,0;11,0)::(26,0;27,0)::(11,0;11,0)::(28,0;11,0)::(29,0;2,0)::(11,0;11,0)::(30,0;11,0)::(31,0;32,0)::(11,0;11,0)::(33,0;6,0)::(11,0;11,0)::(34,0;11,0)::(11,0;11,0)::(35,0;36,0)::(11,0;11,0)::(19,0;11,0)::nil)))::

(makeTM BR1 ER0 CR0 AR0 DL1 HR1 AL1 BL0 AR1 CL0,
WA 2
47 (WDFA_from_list ((0,0;1,0)::(2,0;3,0)::(4,0;5,0)::(6,0;7,0)::(8,0;9,0)::(10,0;11,0)::(12,0;11,0)::(13,1;1,1)::(11,0;11,0)::(14,0;11,0)::(15,0;16,0)::(11,0;11,0)::(17,0;18,0)::(19,0;20,0)::(21,0;22,0)::(11,0;11,0)::(23,0;11,0)::(11,0;11,0)::(24,0;11,0)::(25,0;26,0)::(27,0;11,0)::(11,0;11,0)::(28,0;29,0)::(30,0;20,0)::(31,0;32,0)::(11,0;11,0)::(33,0;11,0)::(34,0;5,0)::(35,0;36,0)::(37,0;11,0)::(11,0;11,0)::(11,0;11,0)::(38,0;11,0)::(39,0;40,0)::(11,0;11,0)::(11,0;11,0)::(41,0;11,0)::(11,0;11,0)::(42,0;43,0)::(11,0;11,0)::(44,0;11,0)::(8,0;9,0)::(11,0;11,0)::(12,0;11,0)::(45,0;46,0)::(11,0;11,0)::(47,0;11,0)::(25,0;26,0)::nil))
64 (WDFA_from_list ((0,0;1,0)::(2,0;3,0)::(4,0;5,0)::(6,0;7,0)::(8,0;9,0)::(10,0;11,0)::(12,0;13,0)::(12,0;12,0)::(14,-1;15,0)::(16,0;17,0)::(12,0;18,0)::(19,0;20,0)::(12,0;12,0)::(21,0;22,0)::(4,0;23,0)::(24,0;25,0)::(12,0;12,0)::(26,0;27,0)::(28,0;29,0)::(12,0;30,0)::(12,0;12,0)::(12,0;31,0)::(12,0;12,0)::(32,0;33,0)::(12,0;34,0)::(35,0;36,0)::(12,0;37,0)::(12,0;12,0)::(12,0;38,0)::(12,0;12,0)::(39,0;40,0)::(41,0;42,0)::(12,0;12,0)::(19,0;20,0)::(43,0;44,0)::(12,-2;45,0)::(12,0;12,0)::(46,0;47,0)::(48,0;49,0)::(12,0;50,0)::(12,0;12,0)::(12,0;51,0)::(12,0;12,0)::(12,0;4,0)::(12,0;12,0)::(52,0;53,0)::(12,0;54,0)::(12,0;12,0)::(12,0;55,0)::(12,0;12,0)::(23,0;56,0)::(6,0;7,0)::(12,-2;57,0)::(12,0;12,0)::(58,0;59,0)::(60,0;61,0)::(12,0;12,0)::(62,0;63,0)::(12,0;17,0)::(12,0;12,0)::(12,0;18,0)::(12,0;12,0)::(12,-2;64,0)::(12,0;12,0)::(35,0;36,0)::nil)))::

(makeTM BR1 DL0 CR1 AR0 DR0 BR0 EL1 HR1 BL1 CL0,
WA 2
49 (WDFA_from_list ((0,0;1,0)::(2,0;3,0)::(4,0;5,0)::(6,0;7,0)::(8,0;9,0)::(10,0;11,0)::(12,0;11,0)::(13,1;1,1)::(11,0;11,0)::(14,0;11,0)::(15,0;16,0)::(11,0;11,0)::(17,0;18,0)::(19,0;20,0)::(21,0;22,0)::(11,0;11,0)::(23,0;11,0)::(11,0;11,0)::(24,0;11,0)::(25,0;26,0)::(27,0;11,0)::(11,0;11,0)::(28,0;29,0)::(30,0;20,0)::(31,0;32,0)::(11,0;11,0)::(33,0;11,0)::(34,0;5,0)::(35,0;36,0)::(37,0;11,0)::(11,0;11,0)::(11,0;11,0)::(38,0;11,0)::(39,0;40,0)::(11,0;11,0)::(11,0;11,0)::(4,0;5,0)::(41,0;42,0)::(43,0;44,0)::(11,0;11,0)::(45,0;11,0)::(11,0;11,0)::(46,0;11,0)::(11,0;11,0)::(12,0;11,0)::(47,0;48,0)::(11,0;11,0)::(11,0;11,0)::(49,0;11,0)::(25,0;26,0)::nil))
69 (WDFA_from_list ((0,0;1,0)::(2,0;3,0)::(4,0;5,0)::(6,0;6,0)::(7,0;8,0)::(9,0;10,0)::(6,0;6,0)::(11,0;12,0)::(13,0;14,0)::(15,0;16,0)::(17,0;18,0)::(19,0;20,0)::(21,0;22,0)::(6,0;23,0)::(16,0;24,0)::(25,0;26,0)::(27,0;28,0)::(6,0;2,0)::(6,0;6,0)::(7,-1;29,0)::(30,0;31,0)::(6,0;6,0)::(26,0;32,0)::(17,0;18,0)::(6,0;6,0)::(9,-1;33,0)::(34,0;35,0)::(6,0;6,0)::(36,0;37,0)::(38,0;39,0)::(6,0;6,0)::(40,0;41,0)::(6,0;6,0)::(42,0;43,0)::(6,0;6,0)::(44,0;45,0)::(6,0;46,0)::(6,0;6,0)::(6,0;47,0)::(48,0;49,0)::(6,0;50,0)::(6,0;6,0)::(6,0;11,0)::(51,0;52,0)::(6,0;53,0)::(6,0;6,0)::(54,0;55,0)::(56,0;57,0)::(6,-2;58,0)::(6,0;6,0)::(51,0;52,0)::(6,-2;59,0)::(6,0;6,0)::(12,0;60,0)::(6,0;61,0)::(6,0;6,0)::(6,0;11,0)::(6,0;6,0)::(62,0;63,0)::(64,0;65,0)::(6,0;6,0)::(16,0;24,0)::(6,-2;66,0)::(6,0;6,0)::(6,-2;31,0)::(6,0;6,0)::(67,0;68,0)::(6,-2;69,0)::(6,0;6,0)::(48,0;49,0)::nil)))::

nil.





Definition check_tms(ls:list ((TM Σ)*DeciderType)):=
  map (fun (x:(TM Σ)*DeciderType)=> let (tm,d):=x in getDecider d tm) ls.

(*
Compute (length tm_WA).
Time Definition check_res := Eval vm_compute in (check_tms ((tm_WA))).
Compute (filter (fun x => match x with Result_NonHalt => false | _ => true end) check_res).
Compute check_res.
*)


Definition tm_list :=
  tm_RWL::
  tm_NG0::tm_NG2::tm_NG3::tm_NG4::tm_NG5::tm_NG6::tm_NG7::tm_NG_ge8::
  tm_Ha::
  tm_Lp1::
  tm_NG_LRU::
  tm_NG0'::tm_RWL'::
  tm_DNV::tm_WA::
  (map (fun tm => (tm,Holdout)) tm_holdouts_13)::
  nil.


Definition TM_enc(tm:TM Σ):positive :=
  match TM_to_N tm with
  | N0 => xH
  | Npos v => Pos.succ v
  end.

Fixpoint TM_ins_all(ls:list ((TM Σ)*DeciderType))(mp:PositiveMap.tree DeciderType):PositiveMap.tree DeciderType :=
match ls with
| nil => mp
| (h1,h2)::t => TM_ins_all t (PositiveMap.add (TM_enc h1) h2 mp)
end.

Fixpoint TM_ins_all'(ls:list (list ((TM Σ)*DeciderType)))(mp:PositiveMap.tree DeciderType):PositiveMap.tree DeciderType :=
match ls with
| nil => mp
| h::t => TM_ins_all' t (TM_ins_all h mp)
end.

Time Definition tm_decider_table :=
  Eval vm_compute in (TM_ins_all' tm_list (PositiveMap.empty DeciderType)).

Definition table_based_decider(tm:TM Σ):HaltDecideResult :=
  match PositiveMap.find (TM_enc tm) tm_decider_table with
  | None => Result_Unknown
  | Some d => getDecider d tm
  end.

Lemma table_based_decider_spec: HaltDecider_WF (N.to_nat BB) table_based_decider.
Proof.
  unfold HaltDecider_WF,table_based_decider.
  intros tm.
  destruct (PositiveMap.find (TM_enc tm) tm_decider_table).
  2: trivial.
  apply getDecider_spec.
Qed.

Definition NF_decider(dec:HaltDecider)(tm:TM Σ):HaltDecideResult :=
  match dec (TM_to_NF tm) with
  | Result_NonHalt => Result_NonHalt
  | _ => Result_Unknown
  end.

Lemma NF_decider_spec dec n:
  HaltDecider_WF n dec ->
  HaltDecider_WF n (NF_decider dec).
Proof.
  unfold HaltDecider_WF,NF_decider.
  intro H.
  intro tm.
  specialize (H (TM_to_NF tm)).
  destruct (dec (TM_to_NF tm)).
  1,3: trivial.
  unfold HaltsFromInit.
  unfold HaltsFromInit in H.
  rewrite <-NonHalt_iff.
  rewrite <-NonHalt_iff in H.
  rewrite <-TM_to_NF_spec in H.
  apply H.
Qed.

Definition decider_all :=
  (HaltDecider_list
(decider2::decider3::decider4::decider5::decider6::decider7::decider8::
decider9::decider10::
decider11::decider12::
decider13::decider14::
table_based_decider::
(NF_decider table_based_decider)::
nil)).

Lemma decider_all_spec: HaltDecider_WF (N.to_nat BB) decider_all.
Proof.
  unfold decider_all,HaltDecider_list.
  repeat apply HaltDecider_cons_spec.
  all: try apply NGramCPS_decider_impl2_spec.
  all: try apply NGramCPS_decider_impl1_spec.
  - apply decider2_WF.
  - apply loop1_decider_WF.
    unfold BB. lia.
  - apply table_based_decider_spec.
  - apply NF_decider_spec,table_based_decider_spec.
  - unfold HaltDecider_nil,HaltDecider_WF.
    intro. trivial.
Qed.





Definition q0 := root_q_upd1_simplified.

Definition q_suc:SearchQueue->SearchQueue := (fun x => SearchQueue_upds x decider_all 20).

Definition q_0 := q0.



Definition q_1_def := q_suc q_0.
Time Definition q_1 := Eval vm_compute in q_1_def.
Definition q_2_def := q_suc q_1.
Time Definition q_2 := Eval vm_compute in q_2_def.
Definition q_3_def := q_suc q_2.
Time Definition q_3 := Eval vm_compute in q_3_def.
Definition q_4_def := q_suc q_3.
Time Definition q_4 := Eval vm_compute in q_4_def.
Definition q_5_def := q_suc q_4.
Time Definition q_5 := Eval vm_compute in q_5_def.
Definition q_6_def := q_suc q_5.
Time Definition q_6 := Eval vm_compute in q_6_def.
Definition q_7_def := q_suc q_6.
Time Definition q_7 := Eval vm_compute in q_7_def.
Definition q_8_def := q_suc q_7.
Time Definition q_8 := Eval vm_compute in q_8_def.
Definition q_9_def := q_suc q_8.
Time Definition q_9 := Eval vm_compute in q_9_def.
Definition q_10_def := q_suc q_9.
Time Definition q_10 := Eval vm_compute in q_10_def.
Definition q_11_def := q_suc q_10.
Time Definition q_11 := Eval vm_compute in q_11_def.
Definition q_12_def := q_suc q_11.
Time Definition q_12 := Eval vm_compute in q_12_def.
Definition q_13_def := q_suc q_12.
Time Definition q_13 := Eval vm_compute in q_13_def.
Definition q_14_def := q_suc q_13.
Time Definition q_14 := Eval vm_compute in q_14_def.
Definition q_15_def := q_suc q_14.
Time Definition q_15 := Eval vm_compute in q_15_def.
Definition q_16_def := q_suc q_15.
Time Definition q_16 := Eval vm_compute in q_16_def.
Definition q_17_def := q_suc q_16.
Time Definition q_17 := Eval vm_compute in q_17_def.
Definition q_18_def := q_suc q_17.
Time Definition q_18 := Eval vm_compute in q_18_def.
Definition q_19_def := q_suc q_18.
Time Definition q_19 := Eval vm_compute in q_19_def.
Definition q_20_def := q_suc q_19.
Time Definition q_20 := Eval vm_compute in q_20_def.
Definition q_21_def := q_suc q_20.
Time Definition q_21 := Eval vm_compute in q_21_def.
Definition q_22_def := q_suc q_21.
Time Definition q_22 := Eval vm_compute in q_22_def.
Definition q_23_def := q_suc q_22.
Time Definition q_23 := Eval vm_compute in q_23_def.
Definition q_24_def := q_suc q_23.
Time Definition q_24 := Eval vm_compute in q_24_def.
Definition q_25_def := q_suc q_24.
Time Definition q_25 := Eval vm_compute in q_25_def.
Definition q_26_def := q_suc q_25.
Time Definition q_26 := Eval vm_compute in q_26_def.
Definition q_27_def := q_suc q_26.
Time Definition q_27 := Eval vm_compute in q_27_def.
Definition q_28_def := q_suc q_27.
Time Definition q_28 := Eval vm_compute in q_28_def.
Definition q_29_def := q_suc q_28.
Time Definition q_29 := Eval vm_compute in q_29_def.
Definition q_30_def := q_suc q_29.
Time Definition q_30 := Eval vm_compute in q_30_def.
Definition q_31_def := q_suc q_30.
Time Definition q_31 := Eval vm_compute in q_31_def.
Definition q_32_def := q_suc q_31.
Time Definition q_32 := Eval vm_compute in q_32_def.
Definition q_33_def := q_suc q_32.
Time Definition q_33 := Eval vm_compute in q_33_def.
Definition q_34_def := q_suc q_33.
Time Definition q_34 := Eval vm_compute in q_34_def.
Definition q_35_def := q_suc q_34.
Time Definition q_35 := Eval vm_compute in q_35_def.
Definition q_36_def := q_suc q_35.
Time Definition q_36 := Eval vm_compute in q_36_def.
Definition q_37_def := q_suc q_36.
Time Definition q_37 := Eval vm_compute in q_37_def.
Definition q_38_def := q_suc q_37.
Time Definition q_38 := Eval vm_compute in q_38_def.
Definition q_39_def := q_suc q_38.
Time Definition q_39 := Eval vm_compute in q_39_def.
Definition q_40_def := q_suc q_39.
Time Definition q_40 := Eval vm_compute in q_40_def.
Definition q_41_def := q_suc q_40.
Time Definition q_41 := Eval vm_compute in q_41_def.
Definition q_42_def := q_suc q_41.
Time Definition q_42 := Eval vm_compute in q_42_def.
Definition q_43_def := q_suc q_42.
Time Definition q_43 := Eval vm_compute in q_43_def.
Definition q_44_def := q_suc q_43.
Time Definition q_44 := Eval vm_compute in q_44_def.
Definition q_45_def := q_suc q_44.
Time Definition q_45 := Eval vm_compute in q_45_def.
Definition q_46_def := q_suc q_45.
Time Definition q_46 := Eval vm_compute in q_46_def.
Definition q_47_def := q_suc q_46.
Time Definition q_47 := Eval vm_compute in q_47_def.
Definition q_48_def := q_suc q_47.
Time Definition q_48 := Eval vm_compute in q_48_def.
Definition q_49_def := q_suc q_48.
Time Definition q_49 := Eval vm_compute in q_49_def.
Definition q_50_def := q_suc q_49.
Time Definition q_50 := Eval vm_compute in q_50_def.
Definition q_51_def := q_suc q_50.
Time Definition q_51 := Eval vm_compute in q_51_def.
Definition q_52_def := q_suc q_51.
Time Definition q_52 := Eval vm_compute in q_52_def.
Definition q_53_def := q_suc q_52.
Time Definition q_53 := Eval vm_compute in q_53_def.
Definition q_54_def := q_suc q_53.
Time Definition q_54 := Eval vm_compute in q_54_def.
Definition q_55_def := q_suc q_54.
Time Definition q_55 := Eval vm_compute in q_55_def.
Definition q_56_def := q_suc q_55.
Time Definition q_56 := Eval vm_compute in q_56_def.
Definition q_57_def := q_suc q_56.
Time Definition q_57 := Eval vm_compute in q_57_def.
Definition q_58_def := q_suc q_57.
Time Definition q_58 := Eval vm_compute in q_58_def.
Definition q_59_def := q_suc q_58.
Time Definition q_59 := Eval vm_compute in q_59_def.
Definition q_60_def := q_suc q_59.
Time Definition q_60 := Eval vm_compute in q_60_def.
Definition q_61_def := q_suc q_60.
Time Definition q_61 := Eval vm_compute in q_61_def.
Definition q_62_def := q_suc q_61.
Time Definition q_62 := Eval vm_compute in q_62_def.
Definition q_63_def := q_suc q_62.
Time Definition q_63 := Eval vm_compute in q_63_def.
Definition q_64_def := q_suc q_63.
Time Definition q_64 := Eval vm_compute in q_64_def.
Definition q_65_def := q_suc q_64.
Time Definition q_65 := Eval vm_compute in q_65_def.
Definition q_66_def := q_suc q_65.
Time Definition q_66 := Eval vm_compute in q_66_def.
Definition q_67_def := q_suc q_66.
Time Definition q_67 := Eval vm_compute in q_67_def.
Definition q_68_def := q_suc q_67.
Time Definition q_68 := Eval vm_compute in q_68_def.
Definition q_69_def := q_suc q_68.
Time Definition q_69 := Eval vm_compute in q_69_def.
Definition q_70_def := q_suc q_69.
Time Definition q_70 := Eval vm_compute in q_70_def.
Definition q_71_def := q_suc q_70.
Time Definition q_71 := Eval vm_compute in q_71_def.
Definition q_72_def := q_suc q_71.
Time Definition q_72 := Eval vm_compute in q_72_def.
Definition q_73_def := q_suc q_72.
Time Definition q_73 := Eval vm_compute in q_73_def.
Definition q_74_def := q_suc q_73.
Time Definition q_74 := Eval vm_compute in q_74_def.
Definition q_75_def := q_suc q_74.
Time Definition q_75 := Eval vm_compute in q_75_def.
Definition q_76_def := q_suc q_75.
Time Definition q_76 := Eval vm_compute in q_76_def.
Definition q_77_def := q_suc q_76.
Time Definition q_77 := Eval vm_compute in q_77_def.
Definition q_78_def := q_suc q_77.
Time Definition q_78 := Eval vm_compute in q_78_def.
Definition q_79_def := q_suc q_78.
Time Definition q_79 := Eval vm_compute in q_79_def.
Definition q_80_def := q_suc q_79.
Time Definition q_80 := Eval vm_compute in q_80_def.
Definition q_81_def := q_suc q_80.
Time Definition q_81 := Eval vm_compute in q_81_def.
Definition q_82_def := q_suc q_81.
Time Definition q_82 := Eval vm_compute in q_82_def.
Definition q_83_def := q_suc q_82.
Time Definition q_83 := Eval vm_compute in q_83_def.
Definition q_84_def := q_suc q_83.
Time Definition q_84 := Eval vm_compute in q_84_def.
Definition q_85_def := q_suc q_84.
Time Definition q_85 := Eval vm_compute in q_85_def.
Definition q_86_def := q_suc q_85.
Time Definition q_86 := Eval vm_compute in q_86_def.
Definition q_87_def := q_suc q_86.
Time Definition q_87 := Eval vm_compute in q_87_def.
Definition q_88_def := q_suc q_87.
Time Definition q_88 := Eval vm_compute in q_88_def.
Definition q_89_def := q_suc q_88.
Time Definition q_89 := Eval vm_compute in q_89_def.
Definition q_90_def := q_suc q_89.
Time Definition q_90 := Eval vm_compute in q_90_def.
Definition q_91_def := q_suc q_90.
Time Definition q_91 := Eval vm_compute in q_91_def.
Definition q_92_def := q_suc q_91.
Time Definition q_92 := Eval vm_compute in q_92_def.
Definition q_93_def := q_suc q_92.
Time Definition q_93 := Eval vm_compute in q_93_def.
Definition q_94_def := q_suc q_93.
Time Definition q_94 := Eval vm_compute in q_94_def.
Definition q_95_def := q_suc q_94.
Time Definition q_95 := Eval vm_compute in q_95_def.
Definition q_96_def := q_suc q_95.
Time Definition q_96 := Eval vm_compute in q_96_def.
Definition q_97_def := q_suc q_96.
Time Definition q_97 := Eval vm_compute in q_97_def.
Definition q_98_def := q_suc q_97.
Time Definition q_98 := Eval vm_compute in q_98_def.
Definition q_99_def := q_suc q_98.
Time Definition q_99 := Eval vm_compute in q_99_def.
Definition q_100_def := q_suc q_99.
Time Definition q_100 := Eval vm_compute in q_100_def.
Definition q_101_def := q_suc q_100.
Time Definition q_101 := Eval vm_compute in q_101_def.
Definition q_102_def := q_suc q_101.
Time Definition q_102 := Eval vm_compute in q_102_def.
Definition q_103_def := q_suc q_102.
Time Definition q_103 := Eval vm_compute in q_103_def.
Definition q_104_def := q_suc q_103.
Time Definition q_104 := Eval vm_compute in q_104_def.
Definition q_105_def := q_suc q_104.
Time Definition q_105 := Eval vm_compute in q_105_def.
Definition q_106_def := q_suc q_105.
Time Definition q_106 := Eval vm_compute in q_106_def.
Definition q_107_def := q_suc q_106.
Time Definition q_107 := Eval vm_compute in q_107_def.
Definition q_108_def := q_suc q_107.
Time Definition q_108 := Eval vm_compute in q_108_def.
Definition q_109_def := q_suc q_108.
Time Definition q_109 := Eval vm_compute in q_109_def.
Definition q_110_def := q_suc q_109.
Time Definition q_110 := Eval vm_compute in q_110_def.
Definition q_111_def := q_suc q_110.
Time Definition q_111 := Eval vm_compute in q_111_def.
Definition q_112_def := q_suc q_111.
Time Definition q_112 := Eval vm_compute in q_112_def.
Definition q_113_def := q_suc q_112.
Time Definition q_113 := Eval vm_compute in q_113_def.
Definition q_114_def := q_suc q_113.
Time Definition q_114 := Eval vm_compute in q_114_def.
Definition q_115_def := q_suc q_114.
Time Definition q_115 := Eval vm_compute in q_115_def.
Definition q_116_def := q_suc q_115.
Time Definition q_116 := Eval vm_compute in q_116_def.
Definition q_117_def := q_suc q_116.
Time Definition q_117 := Eval vm_compute in q_117_def.
Definition q_118_def := q_suc q_117.
Time Definition q_118 := Eval vm_compute in q_118_def.
Definition q_119_def := q_suc q_118.
Time Definition q_119 := Eval vm_compute in q_119_def.
Definition q_120_def := q_suc q_119.
Time Definition q_120 := Eval vm_compute in q_120_def.
Definition q_121_def := q_suc q_120.
Time Definition q_121 := Eval vm_compute in q_121_def.
Definition q_122_def := q_suc q_121.
Time Definition q_122 := Eval vm_compute in q_122_def.
Definition q_123_def := q_suc q_122.
Time Definition q_123 := Eval vm_compute in q_123_def.
Definition q_124_def := q_suc q_123.
Time Definition q_124 := Eval vm_compute in q_124_def.
Definition q_125_def := q_suc q_124.
Time Definition q_125 := Eval vm_compute in q_125_def.
Definition q_126_def := q_suc q_125.
Time Definition q_126 := Eval vm_compute in q_126_def.
Definition q_127_def := q_suc q_126.
Time Definition q_127 := Eval vm_compute in q_127_def.
Definition q_128_def := q_suc q_127.
Time Definition q_128 := Eval vm_compute in q_128_def.
Definition q_129_def := q_suc q_128.
Time Definition q_129 := Eval vm_compute in q_129_def.
Definition q_130_def := q_suc q_129.
Time Definition q_130 := Eval vm_compute in q_130_def.
Definition q_131_def := q_suc q_130.
Time Definition q_131 := Eval vm_compute in q_131_def.
Definition q_132_def := q_suc q_131.
Time Definition q_132 := Eval vm_compute in q_132_def.
Definition q_133_def := q_suc q_132.
Time Definition q_133 := Eval vm_compute in q_133_def.
Definition q_134_def := q_suc q_133.
Time Definition q_134 := Eval vm_compute in q_134_def.
Definition q_135_def := q_suc q_134.
Time Definition q_135 := Eval vm_compute in q_135_def.
Definition q_136_def := q_suc q_135.
Time Definition q_136 := Eval vm_compute in q_136_def.
Definition q_137_def := q_suc q_136.
Time Definition q_137 := Eval vm_compute in q_137_def.
Definition q_138_def := q_suc q_137.
Time Definition q_138 := Eval vm_compute in q_138_def.
Definition q_139_def := q_suc q_138.
Time Definition q_139 := Eval vm_compute in q_139_def.
Definition q_140_def := q_suc q_139.
Time Definition q_140 := Eval vm_compute in q_140_def.
Definition q_141_def := q_suc q_140.
Time Definition q_141 := Eval vm_compute in q_141_def.
Definition q_142_def := q_suc q_141.
Time Definition q_142 := Eval vm_compute in q_142_def.
Definition q_143_def := q_suc q_142.
Time Definition q_143 := Eval vm_compute in q_143_def.
Definition q_144_def := q_suc q_143.
Time Definition q_144 := Eval vm_compute in q_144_def.
Definition q_145_def := q_suc q_144.
Time Definition q_145 := Eval vm_compute in q_145_def.
Definition q_146_def := q_suc q_145.
Time Definition q_146 := Eval vm_compute in q_146_def.
Definition q_147_def := q_suc q_146.
Time Definition q_147 := Eval vm_compute in q_147_def.
Definition q_148_def := q_suc q_147.
Time Definition q_148 := Eval vm_compute in q_148_def.
Definition q_149_def := q_suc q_148.
Time Definition q_149 := Eval vm_compute in q_149_def.
Definition q_150_def := q_suc q_149.
Time Definition q_150 := Eval vm_compute in q_150_def.
Definition q_151_def := q_suc q_150.
Time Definition q_151 := Eval vm_compute in q_151_def.
Definition q_152_def := q_suc q_151.
Time Definition q_152 := Eval vm_compute in q_152_def.
Definition q_153_def := q_suc q_152.
Time Definition q_153 := Eval vm_compute in q_153_def.
Definition q_154_def := q_suc q_153.
Time Definition q_154 := Eval vm_compute in q_154_def.
Definition q_155_def := q_suc q_154.
Time Definition q_155 := Eval vm_compute in q_155_def.
Definition q_156_def := q_suc q_155.
Time Definition q_156 := Eval vm_compute in q_156_def.
Definition q_157_def := q_suc q_156.
Time Definition q_157 := Eval vm_compute in q_157_def.
Definition q_158_def := q_suc q_157.
Time Definition q_158 := Eval vm_compute in q_158_def.
Definition q_159_def := q_suc q_158.
Time Definition q_159 := Eval vm_compute in q_159_def.
Definition q_160_def := q_suc q_159.
Time Definition q_160 := Eval vm_compute in q_160_def.
Definition q_161_def := q_suc q_160.
Time Definition q_161 := Eval vm_compute in q_161_def.
Definition q_162_def := q_suc q_161.
Time Definition q_162 := Eval vm_compute in q_162_def.
Definition q_163_def := q_suc q_162.
Time Definition q_163 := Eval vm_compute in q_163_def.
Definition q_164_def := q_suc q_163.
Time Definition q_164 := Eval vm_compute in q_164_def.
Definition q_165_def := q_suc q_164.
Time Definition q_165 := Eval vm_compute in q_165_def.
Definition q_166_def := q_suc q_165.
Time Definition q_166 := Eval vm_compute in q_166_def.
Definition q_167_def := q_suc q_166.
Time Definition q_167 := Eval vm_compute in q_167_def.
Definition q_168_def := q_suc q_167.
Time Definition q_168 := Eval vm_compute in q_168_def.
Definition q_169_def := q_suc q_168.
Time Definition q_169 := Eval vm_compute in q_169_def.
Definition q_170_def := q_suc q_169.
Time Definition q_170 := Eval vm_compute in q_170_def.
Definition q_171_def := q_suc q_170.
Time Definition q_171 := Eval vm_compute in q_171_def.
Definition q_172_def := q_suc q_171.
Time Definition q_172 := Eval vm_compute in q_172_def.
Definition q_173_def := q_suc q_172.
Time Definition q_173 := Eval vm_compute in q_173_def.
Definition q_174_def := q_suc q_173.
Time Definition q_174 := Eval vm_compute in q_174_def.
Definition q_175_def := q_suc q_174.
Time Definition q_175 := Eval vm_compute in q_175_def.
Definition q_176_def := q_suc q_175.
Time Definition q_176 := Eval vm_compute in q_176_def.
Definition q_177_def := q_suc q_176.
Time Definition q_177 := Eval vm_compute in q_177_def.
Definition q_178_def := q_suc q_177.
Time Definition q_178 := Eval vm_compute in q_178_def.
Definition q_179_def := q_suc q_178.
Time Definition q_179 := Eval vm_compute in q_179_def.
Definition q_180_def := q_suc q_179.
Time Definition q_180 := Eval vm_compute in q_180_def.
Definition q_181_def := q_suc q_180.
Time Definition q_181 := Eval vm_compute in q_181_def.
Definition q_182_def := q_suc q_181.
Time Definition q_182 := Eval vm_compute in q_182_def.
Definition q_183_def := q_suc q_182.
Time Definition q_183 := Eval vm_compute in q_183_def.
Definition q_184_def := q_suc q_183.
Time Definition q_184 := Eval vm_compute in q_184_def.
Definition q_185_def := q_suc q_184.
Time Definition q_185 := Eval vm_compute in q_185_def.
Definition q_186_def := q_suc q_185.
Time Definition q_186 := Eval vm_compute in q_186_def.
Definition q_187_def := q_suc q_186.
Time Definition q_187 := Eval vm_compute in q_187_def.
Definition q_188_def := q_suc q_187.
Time Definition q_188 := Eval vm_compute in q_188_def.
Definition q_189_def := q_suc q_188.
Time Definition q_189 := Eval vm_compute in q_189_def.
Definition q_190_def := q_suc q_189.
Time Definition q_190 := Eval vm_compute in q_190_def.
Definition q_191_def := q_suc q_190.
Time Definition q_191 := Eval vm_compute in q_191_def.
Definition q_192_def := q_suc q_191.
Time Definition q_192 := Eval vm_compute in q_192_def.
Definition q_193_def := q_suc q_192.
Time Definition q_193 := Eval vm_compute in q_193_def.
Definition q_194_def := q_suc q_193.
Time Definition q_194 := Eval vm_compute in q_194_def.
Definition q_195_def := q_suc q_194.
Time Definition q_195 := Eval vm_compute in q_195_def.
Definition q_196_def := q_suc q_195.
Time Definition q_196 := Eval vm_compute in q_196_def.
Definition q_197_def := q_suc q_196.
Time Definition q_197 := Eval vm_compute in q_197_def.
Definition q_198_def := q_suc q_197.
Time Definition q_198 := Eval vm_compute in q_198_def.
Definition q_199_def := q_suc q_198.
Time Definition q_199 := Eval vm_compute in q_199_def.
Definition q_200_def := q_suc q_199.
Time Definition q_200 := Eval vm_compute in q_200_def.


Lemma iter_S{A}(f:A->A)(x x0:A) n:
  x0 = Nat.iter n f x ->
  f x0 = Nat.iter (S n) f x.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Ltac q_rw q_x q_x_def :=
  assert (H:q_x = q_x_def) by (vm_cast_no_check (eq_refl q_x));
  rewrite H; unfold q_x_def; clear H; apply iter_S.

Lemma q_200_spec: q_200 = Nat.iter 200 q_suc q_0.
q_rw q_200 q_200_def.
q_rw q_199 q_199_def.
q_rw q_198 q_198_def.
q_rw q_197 q_197_def.
q_rw q_196 q_196_def.
q_rw q_195 q_195_def.
q_rw q_194 q_194_def.
q_rw q_193 q_193_def.
q_rw q_192 q_192_def.
q_rw q_191 q_191_def.
q_rw q_190 q_190_def.
q_rw q_189 q_189_def.
q_rw q_188 q_188_def.
q_rw q_187 q_187_def.
q_rw q_186 q_186_def.
q_rw q_185 q_185_def.
q_rw q_184 q_184_def.
q_rw q_183 q_183_def.
q_rw q_182 q_182_def.
q_rw q_181 q_181_def.
q_rw q_180 q_180_def.
q_rw q_179 q_179_def.
q_rw q_178 q_178_def.
q_rw q_177 q_177_def.
q_rw q_176 q_176_def.
q_rw q_175 q_175_def.
q_rw q_174 q_174_def.
q_rw q_173 q_173_def.
q_rw q_172 q_172_def.
q_rw q_171 q_171_def.
q_rw q_170 q_170_def.
q_rw q_169 q_169_def.
q_rw q_168 q_168_def.
q_rw q_167 q_167_def.
q_rw q_166 q_166_def.
q_rw q_165 q_165_def.
q_rw q_164 q_164_def.
q_rw q_163 q_163_def.
q_rw q_162 q_162_def.
q_rw q_161 q_161_def.
q_rw q_160 q_160_def.
q_rw q_159 q_159_def.
q_rw q_158 q_158_def.
q_rw q_157 q_157_def.
q_rw q_156 q_156_def.
q_rw q_155 q_155_def.
q_rw q_154 q_154_def.
q_rw q_153 q_153_def.
q_rw q_152 q_152_def.
q_rw q_151 q_151_def.
q_rw q_150 q_150_def.
q_rw q_149 q_149_def.
q_rw q_148 q_148_def.
q_rw q_147 q_147_def.
q_rw q_146 q_146_def.
q_rw q_145 q_145_def.
q_rw q_144 q_144_def.
q_rw q_143 q_143_def.
q_rw q_142 q_142_def.
q_rw q_141 q_141_def.
q_rw q_140 q_140_def.
q_rw q_139 q_139_def.
q_rw q_138 q_138_def.
q_rw q_137 q_137_def.
q_rw q_136 q_136_def.
q_rw q_135 q_135_def.
q_rw q_134 q_134_def.
q_rw q_133 q_133_def.
q_rw q_132 q_132_def.
q_rw q_131 q_131_def.
q_rw q_130 q_130_def.
q_rw q_129 q_129_def.
q_rw q_128 q_128_def.
q_rw q_127 q_127_def.
q_rw q_126 q_126_def.
q_rw q_125 q_125_def.
q_rw q_124 q_124_def.
q_rw q_123 q_123_def.
q_rw q_122 q_122_def.
q_rw q_121 q_121_def.
q_rw q_120 q_120_def.
q_rw q_119 q_119_def.
q_rw q_118 q_118_def.
q_rw q_117 q_117_def.
q_rw q_116 q_116_def.
q_rw q_115 q_115_def.
q_rw q_114 q_114_def.
q_rw q_113 q_113_def.
q_rw q_112 q_112_def.
q_rw q_111 q_111_def.
q_rw q_110 q_110_def.
q_rw q_109 q_109_def.
q_rw q_108 q_108_def.
q_rw q_107 q_107_def.
q_rw q_106 q_106_def.
q_rw q_105 q_105_def.
q_rw q_104 q_104_def.
q_rw q_103 q_103_def.
q_rw q_102 q_102_def.
q_rw q_101 q_101_def.
q_rw q_100 q_100_def.
q_rw q_99 q_99_def.
q_rw q_98 q_98_def.
q_rw q_97 q_97_def.
q_rw q_96 q_96_def.
q_rw q_95 q_95_def.
q_rw q_94 q_94_def.
q_rw q_93 q_93_def.
q_rw q_92 q_92_def.
q_rw q_91 q_91_def.
q_rw q_90 q_90_def.
q_rw q_89 q_89_def.
q_rw q_88 q_88_def.
q_rw q_87 q_87_def.
q_rw q_86 q_86_def.
q_rw q_85 q_85_def.
q_rw q_84 q_84_def.
q_rw q_83 q_83_def.
q_rw q_82 q_82_def.
q_rw q_81 q_81_def.
q_rw q_80 q_80_def.
q_rw q_79 q_79_def.
q_rw q_78 q_78_def.
q_rw q_77 q_77_def.
q_rw q_76 q_76_def.
q_rw q_75 q_75_def.
q_rw q_74 q_74_def.
q_rw q_73 q_73_def.
q_rw q_72 q_72_def.
q_rw q_71 q_71_def.
q_rw q_70 q_70_def.
q_rw q_69 q_69_def.
q_rw q_68 q_68_def.
q_rw q_67 q_67_def.
q_rw q_66 q_66_def.
q_rw q_65 q_65_def.
q_rw q_64 q_64_def.
q_rw q_63 q_63_def.
q_rw q_62 q_62_def.
q_rw q_61 q_61_def.
q_rw q_60 q_60_def.
q_rw q_59 q_59_def.
q_rw q_58 q_58_def.
q_rw q_57 q_57_def.
q_rw q_56 q_56_def.
q_rw q_55 q_55_def.
q_rw q_54 q_54_def.
q_rw q_53 q_53_def.
q_rw q_52 q_52_def.
q_rw q_51 q_51_def.
q_rw q_50 q_50_def.
q_rw q_49 q_49_def.
q_rw q_48 q_48_def.
q_rw q_47 q_47_def.
q_rw q_46 q_46_def.
q_rw q_45 q_45_def.
q_rw q_44 q_44_def.
q_rw q_43 q_43_def.
q_rw q_42 q_42_def.
q_rw q_41 q_41_def.
q_rw q_40 q_40_def.
q_rw q_39 q_39_def.
q_rw q_38 q_38_def.
q_rw q_37 q_37_def.
q_rw q_36 q_36_def.
q_rw q_35 q_35_def.
q_rw q_34 q_34_def.
q_rw q_33 q_33_def.
q_rw q_32 q_32_def.
q_rw q_31 q_31_def.
q_rw q_30 q_30_def.
q_rw q_29 q_29_def.
q_rw q_28 q_28_def.
q_rw q_27 q_27_def.
q_rw q_26 q_26_def.
q_rw q_25 q_25_def.
q_rw q_24 q_24_def.
q_rw q_23 q_23_def.
q_rw q_22 q_22_def.
q_rw q_21 q_21_def.
q_rw q_20 q_20_def.
q_rw q_19 q_19_def.
q_rw q_18 q_18_def.
q_rw q_17 q_17_def.
q_rw q_16 q_16_def.
q_rw q_15 q_15_def.
q_rw q_14 q_14_def.
q_rw q_13 q_13_def.
q_rw q_12 q_12_def.
q_rw q_11 q_11_def.
q_rw q_10 q_10_def.
q_rw q_9 q_9_def.
q_rw q_8 q_8_def.
q_rw q_7 q_7_def.
q_rw q_6 q_6_def.
q_rw q_5 q_5_def.
q_rw q_4 q_4_def.
q_rw q_3 q_3_def.
q_rw q_2 q_2_def.
q_rw q_1 q_1_def.
reflexivity.
Time Qed.


Lemma q_200_WF:
  SearchQueue_WF (N.to_nat BB) q_200 root.
Proof.
  rewrite q_200_spec.
  generalize 200.
  intro n.
  induction n.
  - replace (Nat.iter 0 q_suc q_0) with q_0 by reflexivity.
    unfold q_0,q0.
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
  TNF_Node_HTUB (N.to_nat BB) root.
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
  HaltTimeUpperBound Σ (N.to_nat BB) (InitES Σ Σ0) (LE Σ (TM0)).
Proof.
  apply root_HTUB.
Qed.

Lemma allTM_HTUB:
  HaltTimeUpperBound Σ (N.to_nat BB) (InitES Σ Σ0) (fun _ => True).
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
  forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB.
Proof.
  intros tm n0.
  apply allTM_HTUB.
  trivial.
Qed.

Lemma BB5_value:
  BB5_value_statement.
Proof.
  split.
  - intros tm n0.
    apply allTM_HTUB.
    trivial.
  - apply BB5_lower_bound.
Qed.

Print Assumptions BB5_value.
End MacroMachine.
























