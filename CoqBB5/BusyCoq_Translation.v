Require Import Lia.
Require Import ZArith.

(* mei's busycoq *)
From BusyCoq Require Import Individual52.
From BusyCoq Require Import Permute.
From BusyCoq Require Import Flip.
From BusyCoq Require Import Compute.
From BusyCoq Require Import TM.

(* mxdys' Coq-BB5 *)
From CoqBB5 Require Import CustomTactics.
From CoqBB5 Require Import BB52Statement.
From CoqBB5 Require Import ListTape.
From CoqBB5 Require Import TM.

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

Definition to_TM(tm:TM.TM):BB52Statement.TM Σ :=
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
  TM.step tm st0 st1 ->
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