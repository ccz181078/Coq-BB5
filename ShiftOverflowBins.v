(** * The representations of binary numbers used by shift-overflow machines *)

(* We import them a bit later because [L] and [R] conflict with [dir] *)
From BusyCoq Require Import Individual52 FixedBin.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
Set Default Goal Selector "!".

Fixpoint L' (n : positive) : side :=
  match n with
  | xH => const 0 <* <[1; 0; 0; 0]
  | xO n => L' n <* <[0; 0; 0; 0]
  | xI n => L' n <* <[1; 0; 0; 0]
  end.

Definition L (n : N) : side :=
  match n with
  | N0 => const 0
  | Npos n => L' n
  end.

Fixpoint R (n : positive) : side :=
  match n with
  | xH => [1; 1] *> const 0
  | xO n => [1; 0] *> R n
  | xI n => [1; 1] *> R n
  end.

Fixpoint K' (n : positive) : side :=
  match n with
  | xH =>    const 0 <* <[1; 0; 0]
  | xO n => K' n <* <[0; 0; 0; 0]
  | xI n => K' n <* <[0; 1; 0; 0]
  end.

Definition K (n : N) : side :=
  match n with
  | N0 => const 0
  | Npos n => K' n
  end.

Lemma L_as_K : forall n,
  L n = K n << 0.
Proof.
  destruct n as [| n].
  - apply const_unfold.
  - simpl. induction n; simpl; try rewrite IHn; reflexivity.
Qed.

Fixpoint Lk {k} (n : bin k) :=
  match n with
  | bb => <[]
  | b0 n => Lk n <+ <[0; 0; 0; 0]
  | b1 n => Lk n <+ <[1; 0; 0; 0]
  end.
