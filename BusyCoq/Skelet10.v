(** * Skelet #10 *)

(** Following https://www.sligocki.com/2023/03/14/skelet-10.html *)

From BusyCoq Require Import Individual52.
From Coq Require Import Lia.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, R, A)
  | B, 0 => Some (0, L, C)  | B, 1 => Some (1, R, A)
  | C, 0 => Some (1, R, E)  | C, 1 => Some (1, L, D)
  | D, 0 => Some (1, L, C)  | D, 1 => Some (0, L, D)
  | E, 0 => None            | E, 1 => Some (0, R, B)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive dorf : Set :=
  | zend : dorf
  | zO : dorf -> dorf
  | zIO : dorf -> dorf.

(* Note: We don't actually need to define [val] for the proof to go
   through. It's just useful to sanity-check the definition. *)
Fixpoint val' (n : dorf) (prev cur : nat) : nat :=
  match n with
  | zend => 0
  | zO n' => val' n' cur (cur + prev)
  | zIO n' => cur + val' n' (cur + prev) (cur + prev + cur)
  end.

Definition val (n : dorf) : nat := val' n 1 1.

Example val_11 : val (zO (zO (zIO (zIO zend)))) = 11.
Proof. reflexivity. Qed.

Fixpoint zI (n : dorf) : dorf :=
  match n with
  | zend => zIO zend
  | zO n' => zIO n'
  (* IIO = OOI *)
  | zIO n' => zO (zO (zI n'))
  end.

Definition incr (n : dorf) : dorf :=
  match n with
  | zend => zIO zend
  | zO n' => zI n'
  | zIO n' => zO (zI n')
  end.

Lemma zI_val' : forall n prev cur,
  val' (zI n) prev cur = cur + val' n cur (cur + prev).
Proof.
  induction n; try reflexivity.
  intros. simpl. rewrite IHn. lia.
Qed.

Lemma incr_val : forall n,
  val (incr n) = S (val n).
Proof.
  intros []; try reflexivity;
  unfold val; simpl; rewrite zI_val'; reflexivity.
Qed.

(** * Right Side Counter *)
Fixpoint Z (n : dorf) : side :=
  match n with
  | zend => const 0
  | zO n' => 0 >> Z n'
  | zIO n' => 1 >> 0 >> Z n'
  end.

Lemma incr_right : forall n l,
  l << 1 {{B}}> Z n -->* l <{{D}} Z (zI n).
Proof.
  induction n; triv.
Qed.

(** * Left Side Counter *)
Fixpoint T (n : dorf) : side :=
  match n with
  | zend => const 0
  | zO n' => T n' <* <[0; 0]
  | zIO n' => T n' <* <[1; 0; 1; 0]
  end.

Definition L (n : dorf) : side :=
  match n with
  | zend => const 0
  | zO n' => T n'
  | zIO n' => T n' <* <[1; 0]
  end.

Lemma incr_left : forall n r,
  T n <{{D}} [1; 1] *> r -->* T (zI n) {{A}}> r.
Proof.
  induction n; triv.
Qed.

(** * Complete Behavior *)
Definition D (n : dorf) : (Q * tape) :=
  L n <{{D}} Z (incr n).

Lemma incr_D : forall n,
  D n -->+ D (incr n).
Proof with execute.
  unfold D.
  destruct n...
  - destruct n.
    + execute.
    + (* zO (zO n) *)
      start_progress.
      follow incr_right...
    + (* zO (zIO n) *)
      start_progress.
      follow incr_left...
  - follow incr_left. start_progress.
    follow incr_right. finish.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (D zend).
  { unfold D. execute. }
  apply progress_nonhalt_simple with (C := D).
  eauto using incr_D.
Qed.
