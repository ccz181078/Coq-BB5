Set Warnings "-abstract-large-number".

Require Import FSets.FMapPositive.
Require Import Lia.
Require Import List.
Require Import ZArith.

From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import BB5_Encodings.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import List_Tape.
From CoqBB5 Require Import Decider_RepWL.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import Deciders_Common.


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
  HaltDecider_WF (N.to_nat BB5_minus_one) dfa_nfa_decider.
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
    destruct s; subst; auto 1; cg.
  - intros.
    remember (S n) as Sn.
    destruct s.
    + subst.
      left. reflexivity.
    + right.
      rewrite in_map_iff.
      exists s.
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
  HaltDecider_WF (N.to_nat BB5_minus_one) (dfa_nfa_verifier n f).
Proof.
  unfold dfa_nfa_verifier.
  apply dfa_nfa_decider_spec.
  - apply nat_n_enc_inj.
  - apply nat_n_list_spec.
Qed.


End DFA_NFA_verifier.