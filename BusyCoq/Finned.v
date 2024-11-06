From BusyCoq Require Import Individual52.
From Coq Require Import Lia PeanoNat.

Ltac deduce_eq0 :=
  lazymatch goal with
  | H: _ + _ = O |- _ =>
    apply Nat.eq_add_0 in H; destruct H
  | H: S _ * _ = O |- _ =>
    apply Nat.eq_mul_0_r in H; [| discriminate]
  | H: ?x = O |- _ =>
    is_var x; subst x
  end.

Ltac single := eapply progress_intro; [prove_step | simpl_tape].
Ltac goto x := lazymatch type of x with
  | I => exists x
  | _ -> I => exists (x ltac:(lia))
  end; single; finish.

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc.
    rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof.
  intros.
  rewrite const_unfold at 1.
  apply align_lpow.
Qed.

Lemma tape_eq_intro : forall (q : Q) (s : Sym) (l r l' r' : side),
  l = l' ->
  r = r' ->
  q;; l {{s}} r = q;; l' {{s}} r'.
Proof. congruence. Qed.

Lemma const_eq_intro : forall (x : Sym) xs,
  xs = const x ->
  x >> xs = const x.
Proof.
  intros. rewrite const_unfold. congruence.
Qed.

Lemma const_eq_intro' : forall (x : Sym) xs,
  const x = xs ->
  const x = x >> xs.
Proof.
  intros. rewrite const_unfold. congruence.
Qed.

Ltac align_tape := repeat
  ((rewrite align_lpow || rewrite align_lpow_const); simpl app).

Tactic Notation "refine_evar" constr(v) uconstr(e) :=
  let n := fresh in
  epose e as n;
  unify v n;
  clear n.

(* evars always on RHS *)
Ltac unify_side :=
  match goal with
  | |- ?x = ?y => reflexivity
  | |- ?s >> ?l = ?s >> ?r => f_equal
  | |- ?x >> ?l = (?x :: ?xs)^^?n *> ?r =>
    is_evar n;
    refine_evar n (S _); simpl; f_equal
  | |- ?s^^?a *> ?l = ?s^^?a' *> ?r =>
    (unify a a' || replace a' with a by lia); f_equal
  | |- _ = ?xs^^?n *> ?r =>
    is_evar n; unify n O; simpl
  | |- ?x >> ?l = const ?x => apply const_eq_intro
  | |- const ?x = ?x >> ?l => apply const_eq_intro'
  end.

Ltac solve_side := repeat unify_side.

Ltac solve_tape :=
  lazymatch goal with
  | |- ?q1;; _ {{?s1}} _ = ?q2;; _ {{?s2}} _ =>
    apply tape_eq_intro; solve_side
  end.

Ltac noop_hook _ := idtac.
Ltac show_leftover _ :=
  match goal with
  | |- ?X => idtac "couldn't prove" X
  end.

Ltac autogoto_tac debug_hook :=
    unshelve eexists;
    [econstructor | simpl; align_tape; single;
     apply evstep_refl'; solve_tape; debug_hook ()]; lia.

Tactic Notation "autogoto" := autogoto_tac noop_hook.
Tactic Notation "debug" "autogoto" := autogoto_tac show_leftover.

Ltac maybe_casesplit_at xs :=
  lazymatch xs with
  | _^^?n *> _ =>
    let n' := fresh n "'" in
    destruct n as [| n']; try lia; repeat deduce_eq0
  | _ => idtac
  end.

Ltac maybe_casesplit :=
  simpl; lazymatch goal with
  | |- context [ ?q;; ?l {{?s}} ?r -[ ?tm ]->+ _ ] =>
    let instr := eval compute in (tm (q, s)) in
    lazymatch instr with
    | Some (_, L, _) => maybe_casesplit_at l
    | Some (_, R, _) => maybe_casesplit_at r
    end
  end.

Ltac finned_tac debug_hook := repeat maybe_casesplit; autogoto_tac debug_hook.

Tactic Notation "finned" := finned_tac noop_hook.
Tactic Notation "debug" "finned" := finned_tac show_leftover.
