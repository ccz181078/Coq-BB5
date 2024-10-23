Require Import List.
Require Import ZArith.
Require Import Logic.FunctionalExtensionality.
Require Import Lia.
Require Import FSets.FMapPositive.
From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import CustomTactics.

Set Warnings "-abstract-large-number".





































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
  unfold BB5_value_statement.
  split.
  - intros tm n0 H.
    invst H.
    epose proof (allTM_HTUB _ _ _ H0) as H1.
    Unshelve. 2: cbn; trivial.
    unfold BB5.
    unfold BB in H1.
    lia.
  - destruct BB5_lower_bound as [tm H].
    exists tm.
    replace (N.to_nat BB5) with (S (N.to_nat BB)).
    1: ctor; apply H.
    unfold BB,BB5. lia.
Qed.

Print Assumptions BB5_value.
End MacroMachine.
























