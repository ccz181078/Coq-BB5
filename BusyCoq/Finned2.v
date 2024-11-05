(** * Cubic-finned machine #2 (https://bbchallenge.org/8120967) *)

From BusyCoq Require Import Individual52 Finned.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, R, A)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, L, B)
  | C, 0 => Some (0, L, D)  | C, 1 => Some (0, R, A)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, E)
  | E, 0 => None            | E, 1 => Some (0, L, D)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym.

Inductive I : Type :=
  | I0 (a b d : nat)   (E : 2*a + d = b) : I
  | I1 (a b c d : nat) (E : 2*a + d + 2 = b + c) : I
  | I2 (a c d : nat)   (E : 2*a + d + 2 = c) : I
  | I3 (a c d : nat)   (E : 2*a + d + 2 = c) : I
  | I4 (a b c d : nat) (E : 2*a + d = b + c + 1) : I
  | I5 (a b : nat)     (E : 2*a + 1 = b) : I
  | I6 (a b : nat)     (E : 2*a + 2 = b) : I
  | I7 (a b d : nat)   (E : 2*a + 1 = b + 2*d) : I
  | I8 (a b d : nat)   (E : 2*a = b + 2*d) : I
  | I9 (a d : nat)     (E : 2*a + 2 = 2*d) : I
  .

Open Scope sym.

Definition f (i : I) : Q * tape :=
  match i with
  | I0 a b d _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} [1; 0]^^d *> const 0
  | I1 a b c d _ => B;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I2 a c d _ => B;;
    const 0 <* [1]^^a {{0}} 1 >> [1]^^c *> [0; 1]^^d *> const 0
  | I3 a c d _ => C;;
    const 0 <* [1]^^a << 1 {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I4 a b c d _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I5 a b _ => B;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I6 a b _ => C;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I7 a b d _ => D;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [0; 1]^^d *> const 0
  | I8 a b d _ => E;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} 1 >> [0; 1]^^d *> const 0
  | I9 a d _ => D;;
    const 0 <* [1]^^a {{0}} [0; 1]^^d *> const 0
  end.

Theorem nonhalt : ~ halts tm c0.
Proof.
  replace c0 with (A;; const 0 << 0 {{0}} const 0)
    by now rewrite <- const_unfold.
  apply progress_nonhalt_simple with (C := f) (i0 := I0 0 0 0 eq_refl).
  intros []; finned.
Qed.
