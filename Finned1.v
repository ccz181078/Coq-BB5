(** * Cubic-finned machine #1 (https://bbchallenge.org/7763480) *)

From BusyCoq Require Import Individual52 Finned.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, L, E)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, R, B)
  | C, 0 => Some (1, R, D)  | C, 1 => Some (1, L, C)
  | D, 0 => Some (0, L, E)  | D, 1 => Some (0, R, B)
  | E, 0 => None            | E, 1 => Some (1, L, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym.

Inductive I : Type :=
  | I0 (a b c d : nat) (E : 2*a + d = b + c) : I
  | I1 (a b d : nat)   (E : 2*a + d + 1 = b) : I
  | I2 (a b c d : nat) (E : 2*a + d + 3 = b + c) : I
  | I3 (a c d : nat)   (E : 2*a + d + 3 = c) : I
  | I4 (a c d : nat)   (E : 2*a + d + 3 = c) : I
  | I5 (a b c d : nat) (E : 2*a + d = b + c) : I
  | I6 (a b : nat)     (E : 2*a + 2 = b) : I
  | I7 (a b : nat)     (E : 2*a + 3 = b) : I
  | I8 (a b d : nat)   (E : 2*a + 2 = b + 2*d) : I
  | I9 (a b d : nat)   (E : 2*a + 1 = b + 2*d) : I
  .

Open Scope sym.

Definition f (i : I) : Q * tape :=
  match i with
  | I0 a b c d _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} [1]^^c *> [0; 1]^^d *> const 0
  | I1 a b d _ => B;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} [1; 0]^^d *> const 0
  | I2 a b c d _ => C;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I3 a c d _ => C;;
    const 0 <* [1]^^a {{0}} 1 >> [1]^^c *> [0; 1]^^d *> const 0
  | I4 a c d _ => D;;
    const 0 <* [1]^^a << 1 {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I5 a b c d _ => B;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I6 a b _ => C;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I7 a b _ => D;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I8 a b d _ => E;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [0; 1]^^d *> const 0
  | I9 a b d _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} 1 >> [0; 1]^^d *> const 0
  end.

Theorem nonhalt : ~ halts tm c0.
Proof.
  replace c0 with (A;; const 0 << 0 {{0}} const 0)
    by now rewrite <- const_unfold.
  apply progress_nonhalt_simple with (C := f) (i0 := I0 0 0 0 0 eq_refl).
  intros []; finned.
Qed.
