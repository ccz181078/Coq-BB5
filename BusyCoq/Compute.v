(** * Compute: executable Turing machine model *)

(** The model in [TM] uses coinductive, infinite streams, for which
    equality is undecidable, and a step relation, which isn't
    explicitly computable. This is nice for abstract reasoning,
    but not directly usable for deciding Turing machines.
    Here, we'll introduce a computable model, and prove
    that corresponds to the abstract one. *)

From Coq Require Import Bool.
From Coq Require Import Program.Tactics.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Lia.
From BusyCoq Require Export TM.
Set Default Goal Selector "!".

Module Compute (Ctx : Ctx).
  Module TM := TM Ctx. Export TM.

(** During computation, a tape is represented similarly to [tape], but
    with finite lists at each side, implicitly completed with [s0]. *)
Definition ctape : Type := list Sym * Sym * list Sym.

(** Lifting [ctape] into the corresponding [tape]. *)
Fixpoint lift_side (xs : list Sym) : Stream Sym :=
  match xs with
  | [] => const s0
  | x :: xs => Cons x (lift_side xs)
  end.

Definition lift_tape (t : ctape) : tape :=
  match t with (l, s, r) => (lift_side l, s, lift_side r) end.

Definition lift (c : Q * ctape) : Q * tape :=
  match c with (q, t) => (q, lift_tape t) end.

Local Obligation Tactic := intros; subst;
  simpl; rewrite const_unfold; congruence.

(** Deciding whether two [ctape]s correspond to the same [tape]. *)
Program Fixpoint empty_side (xs : list Sym)
    : {lift_side xs = const s0} + {lift_side xs <> const s0} :=
  match xs with
  | x :: xs => eqb_sym x s0 && Reduce (empty_side xs)
  | [] => Yes
  end.

Local Obligation Tactic := intros; subst; simpl in *; try congruence.

Program Fixpoint eqb_side (xs ys : list Sym)
    : {lift_side xs = lift_side ys} + {lift_side xs <> lift_side ys} :=
  match xs with
  | x :: xs' =>
    match ys with
    | y :: ys' => eqb_sym x y && Reduce (eqb_side xs' ys')
    | [] => Reduce (empty_side xs)
    end
  | [] => Reduce (empty_side ys)
  end.

Program Definition eqb_tape (t t' : ctape)
    : {lift_tape t = lift_tape t'} + {lift_tape t <> lift_tape t'} :=
  match t, t' with
  | (l, s, r), (l', s', r') =>
    eqb_side l l' && (eqb_sym s s' && Reduce (eqb_side r r'))
  end.

Program Definition eqb (c c' : Q * ctape)
    : {lift c = lift c'} + {lift c <> lift c'} :=
  match c, c' with
  | q;; t, q';; t' => eqb_q q q' && Reduce (eqb_tape t t')
  end.

(** Movement on [ctape]s. *)
Definition left (t : ctape) : ctape :=
  match t with
  | ([], s, r) => ([], s0, s :: r)
  | (s' :: l, s, r) => (l, s', s :: r)
  end.

Definition right (t : ctape) : ctape :=
  match t with
  | (l, s, []) => (s :: l, s0, [])
  | (l, s, s' :: r) => (s :: l, s', r)
  end.

Arguments left : simpl never.
Arguments right : simpl never.

Lemma lift_left : forall t, lift_tape (left t) = move_left (lift_tape t).
Proof.
  intros [[[| s' l] s] r]; reflexivity.
Qed.

Lemma lift_right : forall t, lift_tape (right t) = move_right (lift_tape t).
Proof.
  intros [[l s] [| s' r]]; reflexivity.
Qed.

#[export] Hint Rewrite lift_left lift_right : core.

Local Obligation Tactic := program_simplify; autorewrite with core; try (apply step_left || apply step_right); eauto.

(** Computable semantics of Turing machines. *)
Program Definition cstep (tm : TM) (c : Q * ctape)
    : {c' | lift c -[ tm ]-> lift c'} + {halted tm (lift c)} :=
  match c with
  | q;; l {{s}} r =>
    match tm (q, s) with
    | None => inright _
    | Some (s', L, q') => [|| q';; left  (l {{s'}} r) ||]
    | Some (s', R, q') => [|| q';; right (l {{s'}} r) ||]
    end
  end.

Program Fixpoint cmultistep (tm : TM) (n : nat) (c : Q * ctape)
    : {c' | lift c -[ tm ]->> n / lift c'} + {halts tm (lift c)} :=
  match n with
  | 0 => [|| c ||]
  | S n' =>
    bind c' <-- cstep tm c;
    bind c'' <-- cmultistep tm n' c';
    [|| c'' ||]
  end.

(** The starting configuration. *)
Definition starting : Q * ctape := q0;; [] {{s0}} [].

Lemma lift_starting : lift starting = c0.
Proof. reflexivity. Qed.

End Compute.
