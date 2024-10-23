Require Import ZArith.
Require Import Lia.
Require Import List.
Require Import FSets.FMapPositive.

From BusyCoq Require Import Prelims.
From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import CustomTactics.
From BusyCoq Require Import CustomListRoutines.
From BusyCoq Require Import Encodings.
From BusyCoq Require Import TM_CoqBB5.

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