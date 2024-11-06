(** * Permute: renaming the states *)

From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Module Permute (Ctx : Ctx).
  Module Flip := Flip Ctx. Export Flip.

(* [f q = q'], where [q] is a state in [tm] and [q'] is the equivalent state
   in [tm']. *)
(* Note that this definition also admits mapping two equivalent states in [tm]
   to the same state in [tm']. This is intentional, though the name isn't
   perfect. *)
Definition Perm (tm tm' : TM) (f : Q -> Q) :=
  (forall q s,
    tm (q, s) = None ->
    tm' (f q, s) = None) /\
  (forall q s s' d q',
    tm (q, s) = Some (s', d, q') ->
    tm' (f q, s) = Some (s', d, f q')).

Lemma perm_halted : forall tm tm' f q t,
  Perm tm tm' f ->
  halted tm (q;; t) ->
  halted tm' (f q;; t).
Proof.
  introv [Hnone Hsome] H.
  destruct t as [[l s] r].
  apply Hnone, H.
Qed.

Lemma perm_halted' : forall tm tm' f q t,
  Perm tm tm' f ->
  halted tm' (f q;; t) ->
  halted tm (q;; t).
Proof.
  introv [Hnone Hsome] H.
  destruct t as [[l s] r].
  unfold halted in *.
  destruct (tm (q, s)) as [[[s' d] q'] |] eqn:E.
  - apply Hsome in E. congruence.
  - congruence.
Qed.

Local Hint Resolve perm_halted perm_halted' : core.

Lemma perm_step : forall tm tm' f q t q' t',
  Perm tm tm' f ->
  q;; t -[ tm ]-> q';; t' ->
  f q;; t -[ tm' ]-> f q';; t'.
Proof.
  introv [Hnone Hsome] Hstep.
  inverts Hstep as Hstep; constructor; auto.
Qed.

Local Hint Resolve perm_step : core.

Lemma perm_step' : forall tm tm' f q t q' t',
  Perm tm tm' f ->
  f q;; t -[ tm' ]-> q';; t' ->
  exists q'', q;; t -[ tm ]-> q'';; t' /\ f q'' = q'.
Proof.
  introv HP Hstep'.
  assert (H1: ~ halted tm' (f q;; t)).
  { introv Hhalt. eapply halted_no_step in Hhalt. eauto. }
  assert (H2: ~ halted tm (q;; t)) by eauto.
  apply no_halted_step in H2. destruct H2 as [[q'' t''] Hstep].
  exists q''.
  assert (f q;; t -[ tm' ]-> f q'';; t'') by eauto.
  assert (f q'';; t'' = q';; t') by eauto using step_deterministic.
  assert (t' = t'') by congruence. subst t''.
  intuition congruence.
Qed.

Lemma perm_multistep : forall tm tm' f,
  Perm tm tm' f -> forall n q t q' t',
  q;; t -[ tm ]->> n / q';; t' ->
  f q;; t -[ tm' ]->> n / f q';; t'.
Proof.
  introv HP.
  induction n; introv Hsteps; inverts Hsteps.
  - auto.
  - destruct c' as [qq tt]. eauto.
Qed.

Local Hint Resolve perm_multistep : core.

Lemma perm_multistep' : forall tm tm' f,
  Perm tm tm' f -> forall n q t q' t',
  f q;; t -[ tm' ]->> n / q';; t' ->
  exists q'', q;; t -[ tm ]->> n / q'';; t' /\ f q'' = q'.
Proof.
  introv HP.
  induction n; introv Hsteps; inverts Hsteps as H1 H2.
  - eauto.
  - destruct c' as [qq tt].
    eapply perm_step' in H1; try eassumption.
    destruct H1 as [qq' [H1 E1]]. subst qq.
    apply IHn in H2.
    jauto.
Qed.

Lemma perm_halts_in : forall tm tm' f q t n,
  Perm tm tm' f ->
  halts_in tm (q;; t) n ->
  halts_in tm' (f q;; t) n.
Proof.
  introv HP Hhalt.
  unfold halts_in in *.
  destruct Hhalt as [[q' t'] [Hstep Hhalt]]. eauto.
Qed.

Lemma perm_halts_in' : forall tm tm' f q t n,
  Perm tm tm' f ->
  halts_in tm' (f q;; t) n ->
  halts_in tm (q;; t) n.
Proof.
  introv HP Hhalt.
  unfold halts_in in *.
  destruct Hhalt as [[q' t'] [Hstep Hhalt]].
  eapply perm_multistep' in Hstep; try eassumption.
  destruct Hstep as [q'' [H E]]. subst q'. eauto.
Qed.

#[export] Hint Resolve perm_halts_in perm_halts_in' : core.

Lemma perm_halts : forall tm tm' f q t,
  Perm tm tm' f ->
  halts tm (q;; t) ->
  halts tm' (f q;; t).
Proof.
  introv HP Hhalts.
  unfold halts in *.
  destruct Hhalts as [n Hhalts]. eauto.
Qed.

Lemma perm_halts' : forall tm tm' f q t,
  Perm tm tm' f ->
  halts tm' (f q;; t) ->
  halts tm (q;; t).
Proof.
  introv HP Hhalts.
  unfold halts in *.
  destruct Hhalts as [n Hhalts]. eauto.
Qed.

Lemma perm_nonhalt : forall tm tm' f q t,
  Perm tm tm' f ->
  ~ halts tm' (f q;; t) ->
  ~ halts tm (q;; t).
Proof.
  introv HP H' H.
  eauto using perm_halts.
Qed.

Lemma perm_nonhalt' : forall tm tm' f q t,
  Perm tm tm' f ->
  ~ halts tm (q;; t) ->
  ~ halts tm' (f q;; t).
Proof.
  introv HP H' H.
  eauto using perm_halts'.
Qed.

End Permute.
