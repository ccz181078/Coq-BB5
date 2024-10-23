Require Import List.
Require Import Lia.
Require Import ZArith.

From BusyCoq Require Import CustomTactics.
From BusyCoq Require Import Prelims.
From BusyCoq Require Import Encodings.
From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import ListTape.
From BusyCoq Require Import Decider_RepWL.
From BusyCoq Require Import Decider_Verifier_FAR.
From BusyCoq Require Import TNF.

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
