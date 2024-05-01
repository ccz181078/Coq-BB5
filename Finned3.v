(** * Cubic-finned machine #3 (https://bbchallenge.org/10756090) *)

From BusyCoq Require Import Individual52 Finned.
Set Default Goal Selector "!".

(* NOTE: this swaps L and R compared to the TNF form *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, L, B)  | A, 1 => Some (1, L, E)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, L, B)
  | C, 0 => Some (0, L, A)  | C, 1 => Some (0, R, D)
  | D, 0 => Some (1, R, B)  | D, 1 => Some (1, R, D)
  | E, 0 => None            | E, 1 => Some (0, L, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Close Scope sym.

Inductive I : Type :=
  | I0 (a b : nat)     (H : 2*a = b + 1) : I
  | I1 (a b : nat)     (H : 2*a = b) : I
  | I2 (a b d : nat)   (H : 2*a = b + 2*d + 1) : I
  | I3 (a b d : nat)   (H : 2*a = b + 2*d + 2) : I
  | I4 (a d : nat)     (H : a = d) : I
  | I5 (a b c d : nat) (H : 2*a + d = b + c) : I
  | I6 (a c d : nat)   (H : 2*a + d = c) : I
  | I7 (a c d : nat)   (H : 2*a + d = c) : I
  | I8 (a b c d : nat) (H : 2*a + d = b + c + 3) : I
  | I9 (a b d : nat)   (H : 2*a + d = b + 2) : I
  .

Open Scope sym.

Definition f (i : I) : Q * tape :=
  match i with
  | I0 a b _ => B;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I1 a b _ => C;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} const 0
  | I2 a b d _ => A;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [0; 1]^^d *> const 0
  | I3 a b d _ => E;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} 1 >> [0; 1]^^d *> const 0
  | I4 a d _ => A;;
    const 0 <* [1]^^a {{0}} [0; 1]^^d *> const 0
  | I5 a b c d _ => B;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I6 a c d _ => B;;
    const 0 <* [1]^^a {{0}} 1 >> [1]^^c *> [0; 1]^^d *> const 0
  | I7 a c d _ => C;;
    const 0 <* [1]^^a << 1 {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I8 a b c d _ => D;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{1}} [1]^^c *> [0; 1]^^d *> const 0
  | I9 a b d _ => D;;
    const 0 <* [1]^^a << 0 <* [1]^^b {{0}} [1; 0]^^d *> const 0
  end.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply progress_nonhalt_simple with (C := f) (i0 := I4 0 0 eq_refl).
  intros []; finned.
Qed.
