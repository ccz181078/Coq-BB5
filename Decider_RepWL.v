Require Import Lia.
Require Import List.
Require Import ZArith.
Require Import FSets.FMapPositive.

From BusyCoq Require Import CustomTactics.
From BusyCoq Require Import Encodings.
From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import Prelims.
From BusyCoq Require Import TM_CoqBB5.
From BusyCoq Require Import ListTape.
From BusyCoq Require Import TNF.
From BusyCoq Require Import Decider_NGramCPS.

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