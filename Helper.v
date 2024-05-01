(** * Various generic lemmas that aren't present in the standard library *)

From Coq Require Import Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Lia.
From Coq Require Import ZifyClasses.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
From Coq Require Import ZArith. Import Nat.
From BusyCoq Require Export LibTactics.
Set Default Goal Selector "!".

(* We are currently in a deprecation cycle where this gets changed
   from [auto with *] to [auto]. Opt in to silence the warning. *)
Ltac Tauto.intuition_solver ::= auto.

(* sig *)
Notation "[: x :]" := (exist _ x _).

(* sumbool *)
Notation Yes := (left _ _).
Notation No := (right _ _).
Notation Reduce x := (if x then Yes else No).
Notation "a && b" := (if a then b else No).

(* sumor *)
Notation "!!" := (inright _).
Notation "[|| x ||]" := (inleft [: x :]).
Notation "'bind' x <- a ; b" := (match a with | [|| x ||] => b | !! => No end)
  (right associativity, at level 60, x pattern).
Notation "'bind' x <-- a ; b" := (match a with | [|| x ||] => b | !! => !! end)
  (right associativity, at level 60, x pattern).

Lemma Cons_unfold : forall A (xs : Stream A),
  xs = Cons (hd xs) (tl xs).
Proof.
  introv. destruct xs. reflexivity.
Qed.

Lemma const_unfold : forall T (x : T),
  const x = Cons x (const x).
Proof.
  introv.
  rewrite Cons_unfold at 1.
  reflexivity.
Qed.

Fixpoint lpow {A} (l : list A) (n : nat) : list A :=
  match n with
  | O => []
  | S n => l ++ lpow l n
  end.

Notation "l ^^ n" := (lpow l n) (at level 20).

Lemma lpow_shift : forall {A} (xs : list A) n,
  xs^^n ++ xs = xs ++ xs^^n.
Proof.
  induction n.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite <- app_assoc, IHn.
    reflexivity.
Qed.

Lemma lpow_add : forall A n m (xs : list A),
  xs^^(n + m) = xs^^n ++ xs^^m.
Proof.
  induction n; introv.
  - reflexivity.
  - simpl. rewrite IHn.
    rewrite app_assoc. reflexivity.
Qed.

Lemma app_cons_r : forall {A} xs (x : A) ys,
  xs ++ x :: ys = (xs ++ [x]) ++ ys.
Proof.
  induction xs.
  - reflexivity.
  - introv. simpl.
    rewrite <- IHxs. reflexivity.
Qed.

Lemma skipn_add : forall {A} n m (xs : list A),
  skipn (n + m) xs = skipn m (skipn n xs).
Proof.
  induction n.
  - reflexivity.
  - destruct xs.
    + repeat rewrite skipn_nil. reflexivity.
    + apply IHn.
Qed.

#[export] Hint Rewrite firstn_nil skipn_nil skipn_all firstn_all
  firstn_app_2 : list.

(** We define our own [reflect] in [Prop] instead of [Set],
    as we don't want it to occur in the extracted programs. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

#[global]
Hint Constructors reflect : core.

Lemma reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  introv H. destruct H; intuition discriminate.
Qed.

Lemma iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  destr_bool; constructor; intuition discriminate.
Qed.

Lemma reflect_sym : forall A (x y : A) b,
  reflect (x = y) b -> reflect (y = x) b.
Proof.
  introv H. destruct H; intuition.
Qed.

Lemma reflect_andb : forall P Q p q,
  reflect P p ->
  reflect Q q ->
  reflect (P /\ Q) (p && q).
Proof.
  introv H1 H2. destruct H1, H2; constructor; intuition.
Qed.

Fixpoint Str_app {A} (xs : list A) (ys : Stream A) : Stream A :=
  match xs with
  | [] => ys
  | x :: xs => Cons x (Str_app xs ys)
  end.

(** Notation for tapes *)
Notation "s >> r" := (Cons s r) (at level 25, right associativity).
Notation "l << s" := (Cons s l) (at level 24, left associativity, only parsing).

Notation "s :> r" := (s :: r) (at level 25, right associativity, only parsing).
Notation "l <: s" := (s :: l) (at level 24, left associativity, only parsing).

Notation "xs +> r" := (xs ++ r) (at level 25, right associativity, only parsing).
Notation "l <+ xs" := (xs ++ l) (at level 24, left associativity, only parsing).

Notation "xs *> r" := (Str_app xs r) (at level 25, right associativity).
Notation "l <* xs" := (Str_app xs l) (at level 24, left associativity, only parsing).

Notation "< [ ]" := nil (only parsing).
Notation "< [ x ; .. ; y ]" := (cons y .. (cons x []) ..) (only parsing).

Lemma Str_app_assoc {A} (xs ys : list A) (zs : Stream A) :
  (xs ++ ys) *> zs = xs *> ys *> zs.
Proof.
  induction xs.
  - reflexivity.
  - simpl. rewrite IHxs. reflexivity.
Qed.

(** Strong induction principles, because the stdlib ones are incomplete
    and I can't get them to work. *)
Lemma strong_induction : forall (P : nat -> Prop),
  (forall n, (forall k, k < n -> P k) -> P n) ->
  forall n, P n.
Proof.
  introv H. introv.
  enough (H' : forall k, k <= n -> P k).
  { apply H'. constructor. }
  induction n; introv G.
  - inverts G. apply H. introv G. inverts G.
  - inverts G.
    + apply H. introv G. apply IHn. lia.
    + auto.
Qed.

Lemma N_strong_induction : forall (P : N -> Prop),
  (forall n, (forall k, (k < n)%N -> P k) -> P n) ->
  forall n, P n.
Proof.
  introv H.
  assert (G: forall n : nat, P (N.of_nat n)).
  { induction n using strong_induction.
    apply H. introv G.
    replace k with (N.of_nat (N.to_nat k))
      by apply N2Nat.id.
    apply H0. lia. }
  introv.
  replace n with (N.of_nat (N.to_nat n))
    by apply N2Nat.id.
  apply G.
Qed.

Lemma positive_strong_induction : forall (P : positive -> Prop),
  (forall n, (forall k, (k < n)%positive -> P k) -> P n) ->
  forall n, P n.
Proof.
  intros P H n.
  replace n with (N.succ_pos (Pos.pred_N n)) by lia.
  apply N_strong_induction with (P := fun n => P (N.succ_pos n)).
  clear n. intros n IH.
  apply H. intros k H'. specialize (IH (Pos.pred_N k)).
  replace (N.succ_pos (Pos.pred_N k)) with k in IH by lia.
  apply IH. lia.
Qed.

(* Heterogenous addition *)
Definition het_add (a : N) (b : positive) : positive :=
  match a with
  | N0 => b
  | Npos a => a + b
  end.

Notation "a :+ b" := (het_add a b)  (at level 50, left associativity).

Lemma het_add_Z : forall a b, Z.pos (a :+ b) = (Z.of_N a + Z.pos b)%Z.
Proof.
  introv. destruct a; unfold ":+"; lia.
Qed.

#[global] Instance Op_het_add : BinOp het_add :=
  { TBOp := Z.add; TBOpInj := het_add_Z }.
Add Zify BinOp Op_het_add.

Lemma het_add_succ_l : forall a b, N.succ a :+ b = Pos.succ (a :+ b).
Proof. lia. Qed.

(* Powers of 2%positive with a nice computational behavior *)
Fixpoint pow2' (k : nat) : positive :=
  match k with
  | O => 1
  | S k => (pow2' k)~0
  end.

Definition pow2 (k : nat) : N := Npos (pow2' k).

Arguments pow2 _ : simpl never.

Lemma pow2_S : forall k,
  pow2 (S k) = N.double (pow2 k).
Proof. introv. unfold pow2. simpl. lia. Qed.

Lemma pow2_gt0 : forall k, (pow2 k > 0)%N.
Proof. unfold pow2. lia. Qed.

Lemma pow2_add : forall n m,
  (pow2' (n + m) = pow2' n * pow2' m)%positive.
Proof.
  introv. induction n; simpl pow2' in *; lia.
Qed.

(** Make [lia] understand [div2] *)
Lemma div2_zify : forall x,
  x = 2 * (div2 x) \/ x = 2 * (div2 x) + 1.
Proof.
  intros.
  repeat rewrite <- double_twice.
  destruct (Even_or_Odd x) as [H | H].
  - apply Even_double in H. lia.
  - apply Odd_double in H. lia.
Qed.

#[global] Instance Op_nat_div2 : UnOp div2 :=
  { TUOp x := (x / 2)%Z;
    TUOpInj x := ltac:(now rewrite div2_div, Nat2Z.inj_div) }.
Add Zify UnOp Op_nat_div2.

(* Make [lia]/[nia] more powerful *)
Lemma length_gt0_if_not_nil : forall A (xs : list A),
  [] <> xs -> length xs <> 0.
Proof. introv H Hlen. apply length_zero_iff_nil in Hlen. auto. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_pre_hook ::=
  unfold pow2 in *; repeat rewrite pow2_add in *; simpl pow2' in *;
  lazymatch goal with
  | H: [] <> _ |- _ => apply length_gt0_if_not_nil in H
  | H: [] = _ -> False |- _ => apply length_gt0_if_not_nil in H
  | _ => idtac
  end.

Section StripPrefix.
  Variable A : Type.
  Variable eqb : forall (a b : A), {a = b} + {a <> b}.

Program Fixpoint strip_prefix (xs ys : list A) : {zs | ys = xs ++ zs} + {True} :=
  match xs, ys with
  | [], ys => [|| ys ||]
  | _, [] => !!
  | x :: xs, y :: ys =>
    if eqb x y then
      match strip_prefix xs ys with
      | [|| zs ||] => [|| zs ||]
      | !! => !!
      end
    else
      !!
  end.
End StripPrefix.

Arguments strip_prefix {A} eqb !xs !ys.
