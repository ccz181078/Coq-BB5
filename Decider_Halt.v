Require Import Lia.
Require Import ZArith.

From BusyCoq Require Import TM_CoqBB5.
From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import CustomTactics.
From BusyCoq Require Import TNF.
From BusyCoq Require Import ListTape.
From BusyCoq Require Import Prelims.

Set Warnings "-abstract-large-number".

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
        unfold ListTape.s,ListTape.m in IHn.
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
    unfold ListTape.s,ListTape.m in H3,H4. subst.
    exists n0. eexists.
    repeat split; eauto 1.
    lia.
  - contradiction.
  - trivial.
Qed.

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
    destruct m; cbn; cg.
  - destruct m.
    + cbn in H. cg.
    + cbn in H.
      specialize (IHn (Pos.pred_N p) H). lia.
Qed.

Definition halt_decider_max := halt_decider 47176870.
Lemma halt_decider_max_spec: HaltDecider_WF (N.to_nat BB5_minus_one) halt_decider_max.
Proof.
  eapply halt_decider_WF.
  unfold BB5_minus_one.
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

