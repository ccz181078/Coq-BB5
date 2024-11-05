(** * Cubic-finned machine #4 (https://bbchallenge.org/11017998) *)

From BusyCoq Require Import Individual52 Finned.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, A)
  | B, 0 => Some (0, L, C)  | B, 1 => Some (0, R, E)
  | C, 0 => None            | C, 1 => Some (1, L, D)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (0, L, C)
  | E, 0 => Some (1, R, A)  | E, 1 => Some (1, R, E)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym.

Inductive I : Type :=
  | I0 (a b : nat)     (H : 2*a = b) : I
  | I1 (a b : nat)     (H : 2*a + 1 = b) : I
  | I2 (a b d : nat)   (H : 2*a = b + 2*d) : I
  | I3 (a b d : nat)   (H : 2*a = b + 2*d + 1) : I
  | I4 (a d : nat)     (H : a = d) : I
  | I5 (a b c d : nat) (H : 2*a + d + 1 = b + c) : I
  | I6 (a c d : nat)   (H : 2*a + d + 1 = c) : I
  | I7 (a c d : nat)   (H : 2*a + d + 1 = c) : I
  | I8 (a b c d : nat) (H : 2*a + d = b + c + 2) : I
  | I9 (a b d : nat)   (H : 2*a + d = b + 1) : I
  .

Open Scope sym.

Definition f (i : I) : Q * tape :=
  match i with
  | I0 a b _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I1 a b _ => B;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I2 a b d _ => C;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [0; 1]^^d *> const 0
  | I3 a b d _ => D;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} 1 >> [0; 1]^^d *> const 0
  | I4 a d _ => D;;
    const 0 <* [1]^^a {{0}} 1 >> [0; 1]^^d *> const 0
  | I5 a b c d _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I6 a c d _ => A;;
    const 0 <* [1]^^a {{0}} 1 >> [1]^^c *> [0; 1]^^d *> const 0
  | I7 a c d _ => B;;
    const 0 <* [1]^^a << 1 {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I8 a b c d _ => E;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I9 a b d _ => E;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} [1; 0]^^d *> const 0
  end.

Theorem nonhalt : ~ halts tm c0.
Proof.
  replace c0 with (A;; const 0 << 0 {{0}} const 0)
    by now rewrite <- const_unfold.
  apply progress_nonhalt_simple with (C := f) (i0 := I0 0 0 eq_refl).
  intros []; finned.
Qed.
