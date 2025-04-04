Require Import ZArith.
Require Import List.
Require Import Lia.

From CoqBB4 Require Import Prelims.
From CoqBB4 Require Import BB4_Encodings.
From CoqBB4 Require Import TM.
From CoqBB4 Require Import BB4_Make_TM.
From CoqBB4 Require Import BB4_Statement.
From CoqBB4 Require Import Tactics.
From CoqBB4 Require Import List_Routines.
From CoqBB4 Require Import Decider_NGramCPS.
From CoqBB4 Require Import TNF.

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


(** The following needs ListES **)
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
