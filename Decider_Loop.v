Require Import Lia.
Require Import List.
Require Import ZArith.

From CoqBB5 Require Import TM_CoqBB5.
From CoqBB5 Require Import BB52Statement.
From CoqBB5 Require Import CustomTactics.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import ListTape.

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

Definition loop1_decider(n:nat)(ns:list nat)(tm:TM Σ):HaltDecideResult :=
  loop1_decider0 tm n {| l:=nil; r:=nil; m:=Σ0; s:=St0 |} Z0 nil (hd O ns) (tl ns).

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
  inversion E0. subst s1.
  repeat split; auto 1.
  2: lia. rewrite <-E0 in H2.
  cbn in H3,H4. subst.
  apply H2.
Qed.