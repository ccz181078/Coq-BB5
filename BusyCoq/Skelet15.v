(** * Skelet #15: #26 with a different initial state *)

From BusyCoq Require Import Individual52.
From Coq Require Import PeanoNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => None
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, L, B)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (1, R, E)
  | D, 0 => Some (1, L, B)  | D, 1 => Some (0, L, D)
  | E, 0 => Some (1, R, A)  | E, 1 => Some (0, R, C)
  end.

From BusyCoq Require Skelet26.

Definition f q :=
  match q with
  | A => E
  | B => C
  | C => A
  | D => B
  | E => D
  end.

Lemma perm : Perm (flip tm) Skelet26.tm f.
Proof.
  split.
  - intros [] []; try discriminate. reflexivity.
  - intros [] [] s' d q' H; inverts H; reflexivity.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply flip_halts_c0.
  eapply perm_nonhalt. { apply perm. }
  apply multistep_nonhalt with (Skelet26.D 0 0 1). { execute. }
  apply Skelet26.D0_nonhalt.
Qed.
