(** * Skelet #17 *)

From BusyCoq Require Import Individual52.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import PeanoNat. Import Nat.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => None
  | B, 0 => Some (0, L, C)  | B, 1 => Some (1, R, E)
  | C, 0 => Some (0, L, D)  | C, 1 => Some (1, L, C)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, B)
  | E, 0 => Some (0, R, B)  | E, 1 => Some (0, R, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation "l <| r" := (l <{{C}} r) (at level 30).
Notation "l |> r" := (l {{B}}> r) (at level 30).


Lemma shift10 : forall n l (i o : Sym),
  l << i << o <* <[i; o]^^n = l <* <[i; o]^^n << i << o.
Proof.
  introv.
  change (l << i << o) with (l <* <[i; o]).
  rewrite lpow_shift'.
  reflexivity.
Qed.

Local Hint Rewrite shift10 : tape_post.

(** ** List-of-exponents representation *)

(* the list starts with the element closest to the tape head *)

(* Note: [lowerL'] and [lowerR'] assume a (10)^n term will get prepended, and
   thus emit the separator for it. This could be written without an auxiliary
   definition, but this form is much easier to state lemmas about. *)
Fixpoint lowerL' (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => lowerL' xs <* <[1; 0]^^x << 1
  end.

Definition lowerL (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => lowerL' xs <* <[1; 0]^^x
  end.

Fixpoint lowerR' (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => 1 >> [1; 0]^^x *> lowerR' xs
  end.

Definition lowerR (xs : list nat) : side :=
  match xs with
  | [] => const 0
  | x::xs => [1; 0]^^x *> lowerR' xs
  end.

Definition lower (xs : list nat) : Q * tape :=
  lowerL xs <| lowerR' [].

Definition lower' (xs : list nat) : Q * tape :=
  lowerL xs |> lowerR' [].

Lemma lowerL_merge : forall x y ys,
  lowerL (y :: ys) <* <[1; 0]^^x = lowerL (x + y :: ys).
Proof.
  introv.
  destruct ys as [| y0 ys]; simpl_tape; reflexivity.
Qed.

Lemma lowerL_nonempty : forall xs,
  xs <> [] ->
  lowerL' xs = lowerL xs << 1.
Proof.
  introv H.
  destruct xs; try congruence.
  reflexivity.
Qed.

Lemma fold_lowerL' : forall x xs,
  lowerL' xs <* <[1; 0]^^x << 1 = lowerL' (x :: xs).
Proof. reflexivity. Qed.


Lemma fold_lowerR' : forall x xs,
  1 >> [1; 0]^^x *> lowerR' xs = lowerR' (x :: xs).
Proof. reflexivity. Qed.

Arguments lowerL : simpl never.
Arguments lowerL' : simpl never.
Arguments lowerR : simpl never.
Arguments lowerR' : simpl never.

(** Basic machine behavior *)

Lemma goright_10 : forall n l r,
  l |> [1; 0]^^n *> r -->* l <* <[1; 0]^^n |> r.
Proof.
  induction n.
  - triv.
  - execute. follow IHn. simpl_tape. finish.
Qed.

Lemma goleft_even10 : forall n l r,
  Even n ->
  l <* <[1; 0]^^n <| r -->* l <| [1; 0]^^n *> r.
Proof.
  introv H. destruct H as [n' H]. rewrite H.
  simpl. rewrite <- plus_n_O. clear n H. rename n' into n.
  simpl_tape.
  generalize dependent l. generalize dependent r.
  induction n; introv.
  - finish.
  - execute. follow IHn. simpl_tape. finish.
Qed.

Lemma goleft_odd10 : forall n l r,
  Even n ->
  l << 1 <* <[1; 0]^^(S n) <| r -->*
  l <* <[1; 0; 1] <* <[1; 0]^^n |> r.
Proof.
  introv H.
  cbn[lpow]. rewrite <- lpow_shift, Str_app_assoc.
  follow goleft_even10. execute.
  follow goright_10. finish.
Qed.

(** ** Higher-level behavior *)

Notation Nonzero := (fun n => n <> O).

Ltac evstep1 := (econstructor; [ econstructor; reflexivity | cbn ]).

Lemma goright_nonzero_step : forall xs x y ys,
  lowerL (y :: ys) |> lowerR' ((S x) :: xs) -->*
  lowerL (x :: (S y) :: ys) |> lowerR' xs.
Proof.
  introv.
  unfold lowerR'. fold lowerR'.
  execute.
  follow goright_10.
  finish.
Qed.


Lemma goright_nonzero_steps : forall xs x y ys zs,
  Forall Nonzero xs ->
  lowerL (y :: ys) |> lowerR' (xs ++ (S x) :: zs) -->*
  lowerL (x :: rev xs ++ (S y) :: ys) |> lowerR' zs.
Proof.
  induction xs; introv Hxs.
  1: apply goright_nonzero_step.
  inverts Hxs as Ha Hxs.
  destruct a as [|a].
  1: congruence.
  eapply evstep_trans.
  2: {
    cbn.
    rewrite <-app_assoc.
    cbn.
    apply IHxs,Hxs.
  }
  cbn.
  apply goright_nonzero_step.
Qed.

Lemma goright_nonzero : forall xs x x' y ys,
  Forall Nonzero xs ->
  lowerL (y :: ys) |> lowerR (x :: xs ++ [S x']) -->*
  lowerL (x' :: rev xs ++ (S x + y) :: ys) |> const 0.
Proof.
  introv Hxs.
  unfold lowerR.
  follow goright_10.
  rewrite lowerL_merge.
  applys_eq goright_nonzero_steps; auto 1.
Qed.


Lemma goright_nonzero' : forall xs x y ys,
  Forall Nonzero xs ->
  lowerL (y :: ys) |> lowerR' (xs ++ [S x]) -->*
  lowerL (x :: rev xs ++ (S y) :: ys) |> const 0.
Proof.
  introv Hxs.
  apply goright_nonzero with (x := O). assumption.
Qed.

Lemma app_nonempty_r : forall A (xs ys : list A),
  ys <> [] -> xs ++ ys <> [].
Proof.
  introv H. destruct xs.
  - apply H.
  - discriminate.
Qed.

Lemma cons_nonempty : forall A (x : A) xs,
  x :: xs <> [].
Proof. discriminate. Qed.

#[export] Hint Resolve app_nonempty_r : core.
#[export] Hint Immediate cons_nonempty : core.

Lemma goleft_even : forall xs l r,
  Forall Even xs ->
  l <> [] ->
  lowerL (xs ++ l) <| lowerR' r -->*
  lowerL l <| lowerR' (rev xs ++ r).
Proof.
  induction xs as [| x xs]; introv Heven Hl.
  - finish.
  - inverts Heven as Hx Hxs.
    simpl lowerL. follow goleft_even10.
    rewrite lowerL_nonempty by auto. execute.
    rewrite fold_lowerR'. follow IHxs.
    rewrite <- app_assoc. finish.
Qed.

#[export] Hint Resolve -> Odd_succ : core.
#[export] Hint Resolve Forall_rev : core.

Lemma increment_S_even : forall x xs y z zs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (S x :: xs ++ y :: z :: zs) -->*
  lower (x :: xs ++ y :: S z :: zs).
Proof.
  introv Hnonzero Heven Hx Hy.
  follow (goleft_even (S x :: xs)).
  destruct y. { destruct Hy. lia. }
  unfold lowerL. rewrite <- fold_lowerL'.
  follow goleft_odd10. (* could get -->+ here *)
  change ([1; 0; 1] *> [0; 1] ^^ z *> lowerL' zs) with
  (1 >> [0; 1]^^(S z) *> lowerL' zs).
  rewrite fold_lowerL'.
  rewrite app_nil_r.
  follow goright_nonzero'.
  rewrite rev_involutive. execute.
Qed.


Lemma increment_O_even : forall x xs y z zs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (O :: S x :: xs ++ y :: z :: zs) -->*
  lower (S x :: xs ++ y :: S z :: zs).
Proof.
  introv Hnonzero Heven Hx Hy.
  remember (lower (S x :: xs ++ y :: S z :: zs)) as tg.
  unfold lower,lowerL.
  cbn.
  unfold lowerL'. fold lowerL'.
  evstep1.
  change (C, ((1 >> [0; 1] ^^ x *> lowerL' (xs ++ y :: z :: zs), 0, 1 >> lowerR' []))) with
  ([0; 1] ^^ (S x) *> lowerL' (xs ++ y :: z :: zs) <| lowerR' [O]).
  follow (goleft_even (S x :: xs)).
  destruct y. { destruct Hy. lia. }
  unfold lowerL. rewrite <- fold_lowerL'.
  follow goleft_odd10. (* could get -->+ here *)
  change ([1; 0; 1] *> [0; 1] ^^ z *> lowerL' zs) with
  (1 >> [0; 1]^^(S z) *> lowerL' zs).
  rewrite fold_lowerL'.
  cbn.
  rewrite <-app_assoc. cbn.
  change [S x; O] with ([S x] ++ [O]).
  change ([0; 1] ^^ y *> lowerL' (S z :: zs)) with (lowerL (y::S z::zs)).
  follow goright_nonzero_steps.
  cbn.
  rewrite rev_involutive.
  subst.
  unfold lowerR'.
  do 3 evstep1.
  rewrite <-const_unfold.
  finish.
Qed.

#[local] Hint Extern 1 (Even _) => rewrite <- even_spec; reflexivity : core.


Lemma increment_S_odd : forall x y xs,
  Odd (S x) ->
  lower (S x :: y :: xs) -->*
  lower (x :: S y :: xs).
Proof.
  introv Hx. follow goleft_odd10. execute.
Qed.

Lemma increment_O_odd : forall x y xs,
  Odd (S x) ->
  lower (O :: S x :: y :: xs) -->*
  lower (S x :: S y :: xs).
Proof.
  introv Hx.
  remember (lower (S x :: S y :: xs)) as tg.
  unfold lower,lowerL.
  cbn.
  unfold lowerL'. fold lowerL'.
  evstep1.
  follow goleft_odd10.
  cbn.
  unfold lowerR'.
  unfold lower in Heqtg.
  do 3 evstep1.
  subst.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma increment_O : forall xs y z zs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  lower (O :: xs ++ y :: z :: zs) -->*
  lower (xs ++ y :: S z :: zs).
Proof.
  introv Hnonzero Heven Hy.
  destruct y as [|y].
  1: inverts Hy; lia.
  destruct xs as [|x xs].
  - cbn.
    apply increment_O_odd,Hy.
  - cbn.
    inverts Hnonzero as Hx Hxs.
    inverts Heven as Hx' Hxs'.
    destruct x as [|x].
    1: lia.
    apply increment_O_even; auto 1.
Qed.

(* This corresponds to overflow followed by empty in Chris Xu's writeup.
   The config [lower (xs ++ [S y; O])] he lists isn't visited. *)
Lemma overflow_S : forall x xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (S x :: xs ++ [y]) -->*
  lower (x :: xs ++ [S y; 1; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hx Hy.
  follow (goleft_even (S x :: xs)). rewrite app_nil_r.
  destruct y. { destruct Hy. lia. }
  unfold lowerL, lowerL'.
  replace (S y) with (y+1) by lia.
  rewrite lpow_add.
  cbn. rewrite Str_app_assoc. cbn.
  follow goleft_even10. execute.
  change (const 0 << 1 << 1 << 1 << 0 << 1 << 1 << 0)
    with (lowerL [1; 1; 0; 0])%nat.
  follow goright_nonzero. rewrite rev_involutive.
  execute.
Qed.

Lemma overflow_O : forall xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  lower (O :: xs ++ [y]) -->*
  lower (xs ++ [S y; 1; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hy.
  follow (goleft_even (O :: xs)). rewrite app_nil_r.
  destruct y. { destruct Hy. lia. }
  unfold lowerL, lowerL'.
  replace (S y) with (y+1) by lia.
  rewrite lpow_add.
  cbn. rewrite Str_app_assoc. cbn.
  follow goleft_even10. execute.
  change (const 0 << 1 << 1 << 1 << 0 << 1 << 1 << 0)
    with (lowerL [1; 1; 0; 0])%nat.
  destruct xs as [|x xs].
  - cbn.
    unfold lowerR'. cbn.
    follow goright_10.
    do 3 evstep1.
    rewrite <-const_unfold.
    unfold lower,lowerR',lowerL.
    simpl_tape.
    finish.
  - cbn. rewrite <-app_assoc. cbn.
    inverts Hnonzero as Hx Hxs.
    inverts Heven as Hx' Hxs'.
    destruct x as [|x]. 1: lia.
    follow goright_10.
    rewrite lowerL_merge.
    follow goright_nonzero_steps. rewrite rev_involutive.
    do 3 evstep1.
    rewrite <-const_unfold.
    unfold lower,lowerR',lowerL.
    simpl_tape.
    finish.
Qed.

Lemma zero_S : forall x xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Even y ->
  lower (S x :: xs ++ [y]) -->*
  lower (x :: xs ++ [S y; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hx Hy.
  follow (goleft_even (S x :: xs)). rewrite app_nil_r.
  unfold lowerL, lowerL'.
  follow goleft_even10. execute.
  follow goright_10.
  change ([0; 1] ^^ y *> 1>>1>>const 0) with (lowerL [y; 0; 0]%nat).
  follow goright_nonzero_steps. rewrite rev_involutive.
  unfold lower,lowerR'.
  do 1 evstep1.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma zero_O : forall xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even y ->
  lower (O :: xs ++ [y]) -->*
  lower (xs ++ [S y; 0; 0]%nat).
Proof.
  introv Hnonzero Heven Hy.
  follow (goleft_even (O :: xs)). rewrite app_nil_r.
  unfold lowerL, lowerL'.
  follow goleft_even10. execute.
  follow goright_10.
  change ([0; 1] ^^ y *> 1>>1>>const 0) with (lowerL [y; 0; 0]%nat).
  destruct xs as [|x xs].
  - cbn.
    unfold lowerR'. cbn.
    do 3 evstep1.
    rewrite <-const_unfold.
    finish.
  - cbn. rewrite <-app_assoc. cbn.
    inverts Hnonzero as Hx Hxs.
    inverts Heven as Hx' Hxs'.
    destruct x as [|x]. 1: lia.
    follow goright_nonzero_steps. rewrite rev_involutive.
    do 3 evstep1.
    rewrite <-const_unfold.
    finish.
Qed.

(* from here we talk about the operations defined in Chris Xu's paper *)

Inductive Increment: (nat*(list nat))->(nat*(list nat))->Prop :=
| Increment_even x xs y z zs:
  Even x ->
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  Increment
  (S x, xs ++ y :: z :: zs)
  (x, xs ++ y :: S z :: zs)
| Increment_odd x y xs:
  Odd x ->
  Increment
  (S x, y :: xs)
  (x, S y :: xs)
.

Inductive Halve: (nat*(list nat))->(nat*(list nat))->Prop :=
| Halve_intro x xs:
  Halve
  (O, x :: xs)
  (S x, xs)
.

Inductive Zero: (nat*(list nat))->(nat*(list nat))->Prop :=
| Zero_intro x xs y:
  Forall Nonzero xs ->
  Forall Even xs ->
  Even x ->
  Even y ->
  Zero
  (S x, xs ++ [y])
  (x, xs ++ [S y; O; O])
.

Inductive Overflow: (nat*(list nat))->(nat*(list nat))->Prop :=
| Overflow_intro x xs y:
  Forall Nonzero xs ->
  Forall Even xs ->
  Even x ->
  Odd y ->
  Overflow
  (S x, xs ++ [y])
  (S x, xs ++ [S y; O])
.

Inductive TryHalve: (nat*(list nat))->(nat*(list nat))->Prop :=
| TryHalve_1 x xs:
  TryHalve
  (O, x :: xs)
  (S x, xs)
| TryHalve_0 x xs:
  TryHalve
  (S x, xs)
  (S x, xs)
.



(* translation between savask's operations and Chris Xu's operations *)

Inductive toConfig: (nat*(list nat))->(Q*tape)->Prop :=
| toConfig_intro x xs:
  toConfig (S x,xs) (lower (x::xs))
.

Lemma Increment_toConfig s1 s2 s3 c1 c3:
  Increment s1 s2 ->
  TryHalve s2 s3 ->
  toConfig s1 c1 ->
  toConfig s3 c3 ->
  c1 -->* c3.
Proof.
  intros I12 I23 T1 T3.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  destruct s3 as [x3 xs3].
  inverts I12.
  - inverts I23.
    + inverts T1.
      inverts T3.
      rewrite H1.
      follow increment_O. finish.
    + inverts T1.
      inverts T3.
      follow increment_S_even.
      finish.
  - inverts I23.
    1: inverts H0; lia.
    inverts T1.
    inverts T3.
    follow increment_S_odd.
    finish.
Qed.

Lemma Zero_toConfig s1 s2 s3 c1 c3:
  Zero s1 s2 ->
  TryHalve s2 s3 ->
  toConfig s1 c1 ->
  toConfig s3 c3 ->
  c1 -->* c3.
Proof.
  intros I12 I23 T1 T3.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  destruct s3 as [x3 xs3].
  inverts I12.
  inverts I23.
  + inverts T1.
    inverts T3.
    rewrite H1.
    follow zero_O. finish.
  + inverts T1.
    inverts T3.
    follow zero_S. finish.
Qed.

Lemma Overflow_toConfig s1 s2 s3 s4 c1 c4:
  Overflow s1 s2 ->
  Zero s2 s3 ->
  TryHalve s3 s4 ->
  toConfig s1 c1 ->
  toConfig s4 c4 ->
  c1 -->* c4.
Proof.
  intros I12 I23 I34 T1 T4.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  destruct s3 as [x3 xs3].
  destruct s4 as [x4 xs4].
  inverts T1.
  inverts T4.
  inverts I12.
  inverts I23.
  inverts I34.
  - follow overflow_O.
    rewrite H2.
    rewrite (app_cons_r xs) in H0.
    rewrite app_inj_tail_iff in H0.
    destruct H0.
    subst.
    rewrite <-app_assoc.
    finish.
  - follow overflow_S.
    rewrite (app_cons_r xs) in H0.
    rewrite app_inj_tail_iff in H0.
    destruct H0.
    subst.
    rewrite <-app_assoc.
    finish.
Qed.


(* decode of Grey Code *)
Fixpoint grey_to_binary(xs:list bool):(list bool) :=
match xs with
| nil => nil
| xh::xt => (xorb xh (hd false (grey_to_binary xt)))::(grey_to_binary xt)
end.

Definition list_to_binary(xs:list nat):(list bool) :=
  grey_to_binary (map odd xs).

Fixpoint binary_to_nat(xs:list bool):nat :=
match xs with
| nil => O
| xh::xt =>
  (if xh then (S O) else O)+(binary_to_nat xt)*2
end.

(* n (binary) *)
Definition to_n_binary(s:nat*(list nat)) :=
  list_to_binary (snd s).

(* n *)
Definition to_n(s:nat*(list nat)) :=
  binary_to_nat (to_n_binary s).

(* s *)
Definition to_s(s:nat*(list nat)) :=
  let (x,xs):=s in
  xorb (even x) (hd false (list_to_binary xs)).

(* l *)
Definition to_l(s:nat*(list nat)) :=
  length (to_n_binary s).


Ltac simpl_xor_neg :=
  repeat (
    rewrite <-Bool.negb_xorb_l ||
    rewrite <-Bool.negb_xorb_r ||
    rewrite Bool.negb_involutive ||
    rewrite Bool.xorb_true_l ||
    rewrite Bool.negb_true_iff ||
    rewrite Bool.negb_false_iff);
  try reflexivity.

Ltac simpl_oe_S :=
  repeat (rewrite odd_succ || rewrite even_succ).

Ltac OE_oe :=
  repeat (match goal with
  | H: Even _ |- _ => rewrite <-even_spec in H
  | H: Odd _ |- _ => rewrite <-odd_spec in H
  end).


(* some trivial lemmas *)

Lemma map_odd_Even xs:
  Forall Even xs ->
  map odd xs = repeat false (length xs).
Proof.
  induction xs.
  1: reflexivity.
  intros Hev.
  inverts Hev as Ha Hxs.
  specialize (IHxs Hxs).
  cbn.
  f_equal; auto 1.
  unfold odd.
  OE_oe.
  rewrite Ha.
  reflexivity.
Qed.

Lemma grey_to_binary_0s_hd n xs:
  hd false (grey_to_binary (repeat false n ++ xs)) = hd false (grey_to_binary xs).
Proof.
  induction n; auto 1.
Qed.

Lemma grey_to_binary_0s n xs:
  grey_to_binary ((repeat false n) ++ xs) =
  (repeat (hd false (grey_to_binary xs)) n) ++ grey_to_binary xs.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite <-IHn.
  f_equal.
  apply grey_to_binary_0s_hd.
Qed.

Lemma hd_repeat(x:bool) n xs:
  hd false ((repeat x n)++x::xs) = x.
Proof.
  destruct n; reflexivity.
Qed.

Lemma repeat_app_S{A} (x:A) n xs:
  repeat x n ++ x :: xs =
  (repeat x (S n)) ++ xs.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite IHn.
  reflexivity.
Qed.

Lemma binary_to_nat_S n xs:
  S (binary_to_nat (repeat true n ++ false :: xs)) =
  binary_to_nat (repeat false n ++ true :: xs).
Proof.
  induction n.
  1: reflexivity.
  cbn.
  rewrite <-IHn.
  lia.
Qed.

Lemma list_to_binary_app_O_hd xs:
  (hd false (list_to_binary (xs ++ [O]))) =
  (hd false (list_to_binary (xs))).
Proof.
  induction xs.
  1: reflexivity.
  cbn.
  unfold list_to_binary in IHxs.
  rewrite IHxs.
  reflexivity.
Qed.

Lemma list_to_binary_S_hd xs z zs:
  (hd false (list_to_binary (xs ++ S z :: zs))) =
  negb (hd false (list_to_binary (xs ++ z :: zs))).
Proof.
  induction xs.
  - cbn.
    simpl_oe_S.
    unfold odd.
    simpl_xor_neg.
  - cbn.
    unfold list_to_binary in IHxs.
    rewrite IHxs.
    simpl_xor_neg.
Qed.

Lemma list_to_binary_app_S_hd xs y:
  (hd false (list_to_binary (xs ++ [S y]))) =
  negb (hd false (list_to_binary (xs ++ [y]))).
Proof.
  induction xs.
  - cbn.
    simpl_oe_S.
    unfold odd.
    simpl_xor_neg.
  - cbn.
    unfold list_to_binary in IHxs.
    rewrite IHxs.
    simpl_xor_neg.
Qed.

Lemma binary_to_nat_app_O xs:
  binary_to_nat (xs ++ [false]) =
  binary_to_nat (xs).
Proof.
  induction xs.
  1: reflexivity.
  cbn.
  rewrite IHxs.
  reflexivity.
Qed.

Lemma pow2_nez i:
  2 ^ i <> O.
Proof.
  apply pow_nonzero; lia.
Qed.

Lemma binary_to_nat_1s_app n xs:
  binary_to_nat (repeat true n ++ xs) =
  (binary_to_nat xs)*(2^n) + (2^n) - 1.
Proof.
  induction n.
  1: cbn; lia.
  cbn.
  rewrite IHn.
  pose proof (pow2_nez n).
  lia.
Qed.

Lemma binary_to_nat_0s_app n xs:
  binary_to_nat (repeat false n ++ xs) =
  (binary_to_nat xs)*(2^n).
Proof.
  induction n.
  1: cbn; lia.
  cbn.
  rewrite IHn.
  pose proof (pow2_nez n).
  lia.
Qed.

Lemma binary_to_nat_1s n:
  binary_to_nat (repeat true n) =
  (2^n)-1.
Proof.
  pose proof (binary_to_nat_1s_app n nil) as H.
  cbn in H.
  rewrite app_nil_r in H.
  apply H.
Qed.

Lemma binary_to_nat_0s n:
  binary_to_nat (repeat false n) =
  O.
Proof.
  pose proof (binary_to_nat_0s_app n nil) as H.
  cbn in H.
  rewrite app_nil_r in H.
  apply H.
Qed.

Lemma grey_to_binary_length xs:
  length (grey_to_binary xs) = length xs.
Proof.
  induction xs.
  1: reflexivity.
  cbn.
  f_equal.
  apply IHxs.
Qed.

Ltac simpl_list_to_binary_0s:=
  unfold list_to_binary;
  rewrite map_app;
  rewrite map_odd_Even; [idtac | auto 1; fail];
  rewrite grey_to_binary_0s;
  cbn;
  try rewrite hd_repeat.




(* s after Inc/Halve/Zero/Overflow *)

Lemma Increment_sgn {s1 s2}:
  Increment s1 s2 ->
  to_s s1 = to_s s2.
Proof.
  intro I.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts I.
  - unfold to_s.
    simpl_oe_S.
    unfold odd.
    symmetry.
    rewrite app_cons_r.
    rewrite list_to_binary_S_hd.
    rewrite <-app_cons_r.
    simpl_xor_neg.
  - unfold to_s.
    simpl_oe_S.
    unfold odd.
    change (S y :: xs) with (nil ++ ((S y :: xs))).
    rewrite (list_to_binary_S_hd). cbn.
    simpl_xor_neg.
Qed.


Lemma Halve_sgn {s1 s2}:
  Halve s1 s2 ->
  negb (to_s s1) = (to_s s2).
Proof.
  intro H.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts H.
  unfold to_s.
  simpl_oe_S.
  cbn.
  unfold list_to_binary.
  destruct (xorb (odd x) (hd false (grey_to_binary (map odd xs2)))); reflexivity.
Qed.


Lemma Zero_sgn {s1 s2}:
  Zero s1 s2 ->
  (to_s s2) = false.
Proof.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  unfold to_s.
  simpl_oe_S.
  OE_oe.
  rewrite H5.
  simpl_xor_neg.
  simpl_list_to_binary_0s.
  simpl_oe_S.
  rewrite H6.
  reflexivity.
Qed.

Lemma Overflow_sgn {s1 s2}:
  Overflow s1 s2 ->
  (to_s s2) = false.
Proof.
  intro Ov.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Ov.
  unfold to_s.
  simpl_oe_S.
  unfold odd.
  OE_oe.
  rewrite H5.
  simpl_xor_neg.
  simpl_list_to_binary_0s.
  simpl_oe_S.
  unfold odd in H6.
  rewrite Bool.negb_true_iff in H6.
  rewrite H6.
  reflexivity.
Qed.

(* trivial properties of the config before Increment *)

Lemma Increment_inc x2 xs y z zs:
  to_s (S x2, xs ++ y :: z :: zs) = true ->
  Even x2 ->
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  (grey_to_binary (map odd (xs ++ y :: z :: zs))) =
  repeat true (S (length xs)) ++ false :: (grey_to_binary (map odd zs)).
Proof.
  intros.
  unfold to_s in H.
  generalize H; clear H.
  simpl_oe_S.
  change (odd x2) with (negb (even x2)).
  OE_oe.
  rewrite H0.
  cbn.
  simpl_list_to_binary_0s.
  rewrite H3.
  simpl_xor_neg.
  destruct (xorb (odd z) (hd false (grey_to_binary (map odd zs)))).
  1: intro X; cbn in X; congruence.
  intro X.
  cbn.
  rewrite repeat_app_S.
  reflexivity.
Qed.

Lemma Increment_dec x2 xs y z zs:
  to_s (S x2, xs ++ y :: z :: zs) = false ->
  Even x2 ->
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  (grey_to_binary (map odd (xs ++ y :: z :: zs))) =
  repeat false (S (length xs)) ++ true :: (grey_to_binary (map odd zs)).
Proof.
  intros.
  unfold to_s in H.
  generalize H; clear H.
  simpl_oe_S.
  change (odd x2) with (negb (even x2)).
  OE_oe.
  rewrite H0.
  cbn.
  simpl_list_to_binary_0s.
  rewrite H3.
  simpl_xor_neg.
  destruct (xorb (odd z) (hd false (grey_to_binary (map odd zs)))).
  2: intro X; cbn in X; congruence.
  intro X.
  cbn.
  rewrite repeat_app_S.
  reflexivity.
Qed.

Lemma Increment_inc_odd x2 y xs:
  to_s (S x2, y :: xs) = true ->
  Odd x2 ->
  (grey_to_binary (map odd (y :: xs))) =
  false :: (grey_to_binary (map odd xs)).
Proof.
  unfold to_s.
  simpl_oe_S.
  intros.
  OE_oe.
  rewrite H0 in H.
  generalize H; clear H.
  simpl_xor_neg.
  cbn.
  congruence.
Qed.

Lemma Increment_dec_odd x2 y xs:
  to_s (S x2, y :: xs) = false ->
  Odd x2 ->
  (grey_to_binary (map odd (y :: xs))) =
  true :: (grey_to_binary (map odd xs)).
Proof.
  unfold to_s.
  simpl_oe_S.
  intros.
  OE_oe.
  rewrite H0 in H.
  generalize H; clear H.
  simpl_xor_neg.
  cbn.
  congruence.
Qed.


Lemma to_s_S x2 xs z zs:
  to_s (x2, xs ++ S z :: zs) =
  negb (to_s (x2, xs ++ z :: zs)).
Proof.
  unfold to_s.
  rewrite list_to_binary_S_hd.
  simpl_xor_neg.
Qed.

Lemma to_s_S' x2 xs y z zs:
  to_s (x2, xs ++ y :: S z :: zs) =
  negb (to_s (x2, xs ++ y :: z :: zs)).
Proof.
  rewrite app_cons_r.
  rewrite to_s_S.
  rewrite <-app_cons_r.
  reflexivity.
Qed.

Lemma to_s_S_odd x2 y zs:
  to_s (x2, S y :: zs) =
  negb (to_s (x2, y :: zs)).
Proof.
  pose proof (to_s_S x2 nil y zs).
  cbn in H. cbn.
  apply H.
Qed.



(* n after Inc/Halve/Zero/Overflow *)

Lemma Increment_n {s1 s2}:
  Increment s1 s2 ->
  if to_s s1 then
  S (to_n s1) = to_n s2
  else
  to_n s1 = S (to_n s2).
Proof.
  destruct (to_s s1) eqn:E.
  {
    intro I.
    destruct s1 as [x1 xs1].
    destruct s2 as [x2 xs2].
    inverts I.
    - cbn.
      rewrite Increment_inc with (x2:=x2); auto 1.
      rewrite Increment_dec with (x2:=x2); auto 1.
      2: rewrite to_s_S',E; reflexivity.
      rewrite binary_to_nat_S.
      reflexivity.
    - unfold to_n,to_n_binary,snd,list_to_binary.
      rewrite Increment_inc_odd with (x2:=x2); auto 1.
      rewrite Increment_dec_odd with (x2:=x2); auto 1.
      rewrite to_s_S_odd,E. reflexivity.
  }
  {
    intro I.
    destruct s1 as [x1 xs1].
    destruct s2 as [x2 xs2].
    inverts I.
    - cbn.
      rewrite Increment_dec with (x2:=x2); auto 1.
      rewrite Increment_inc with (x2:=x2); auto 1.
      2: rewrite to_s_S',E; reflexivity.
      rewrite binary_to_nat_S.
      reflexivity.
    - unfold to_n,to_n_binary,snd,list_to_binary.
      rewrite Increment_dec_odd with (x2:=x2); auto 1.
      rewrite Increment_inc_odd with (x2:=x2); auto 1.
      rewrite to_s_S_odd,E. reflexivity.
  }
Qed.

Lemma Halve_n {s1 s2}:
  Halve s1 s2 ->
  div2 (to_n s1) = to_n s2.
Proof.
  intro H.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts H.
  cbn.
  remember (xorb (odd x) (hd false (grey_to_binary (map odd xs2)))) as v1.
  destruct v1; lia.
Qed.

Lemma Zero_n {s1 s2}:
  Zero s1 s2 ->
  to_n s2 = (2 ^ (to_l s1)) - 1.
Proof.
  unfold to_l.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  unfold to_n_binary,snd,list_to_binary.
  rewrite grey_to_binary_length,length_map,length_app.
  cbn.
  rewrite map_app,map_odd_Even.
  2: auto 1.
  rewrite grey_to_binary_0s.
  OE_oe.
  cbn.
  simpl_oe_S.
  rewrite H6.
  cbn.
  rewrite repeat_app_S.
  rewrite app_cons_r.
  do 2 rewrite binary_to_nat_app_O.
  rewrite binary_to_nat_1s.
  rewrite Nat.add_comm.
  cbn; lia.
Qed.

Lemma Overflow_n {s1 s2}:
  Overflow s1 s2 ->
  to_n s2 = O.
Proof.
  unfold to_l.
  intro Ov.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Ov.
  cbn.
  simpl_list_to_binary_0s.
  simpl_oe_S.
  OE_oe.
  unfold odd in H6.
  rewrite Bool.negb_true_iff in H6.
  rewrite H6.
  cbn.
  rewrite binary_to_nat_0s_app.
  reflexivity.
Qed.



(* l after Inc/Halve/Zero/Overflow *)

Lemma Increment_len {s1 s2}:
  Increment s1 s2 ->
  to_l s1 = to_l s2.
Proof.
  intro I.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts I.
  - cbn.
    repeat rewrite grey_to_binary_length,length_map,length_app.
    reflexivity.
  - reflexivity.
Qed.

Lemma Halve_len {s1 s2}:
  Halve s1 s2 ->
  to_l s1 = S (to_l s2).
Proof.
  intro H.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts H.
  cbn.
  reflexivity.
Qed.

Lemma Zero_len {s1 s2}:
  Zero s1 s2 ->
  to_l s2 = to_l s1 + 2.
Proof.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  cbn.
  repeat rewrite grey_to_binary_length,length_map,length_app.
  cbn.
  lia.
Qed.

Lemma Overflow_len {s1 s2}:
  Overflow s1 s2 ->
  to_l s2 = to_l s1 + 1.
Proof.
  intro Z.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  inverts Z.
  cbn.
  repeat rewrite grey_to_binary_length,length_map,length_app.
  cbn.
  lia.
Qed.




(* <n/2^i> *)

Definition divpow2r(n i:nat) :=
  (n+(2^i))/(2^(i+1)).

Lemma divpow2r_inc n i:
  n mod 2^(i+1) = (2^i)-1 ->
  (divpow2r n i)+1 =
  divpow2r (n+1) i.
Proof.
  unfold divpow2r.
  intro H.
  rewrite (Div0.div_mod n (2 ^ (i + 1))).
  rewrite H.
  pose proof (pow2_nez i) as E.
  remember (n / 2 ^ (i + 1)) as v1.
  rewrite (Nat.add_comm i 1).
  change (2^(1+i)) with (2*2^i).
  replace (2 * 2 ^ i * v1 + (2 ^ i - 1) + 1 + 2 ^ i) with
  ((v1 + 1) * (2 * 2 ^ i)) by lia.
  rewrite Nat.div_mul. 2: lia.
  rewrite <-Nat.add_assoc.
  rewrite (Nat.mul_comm (2*2^i) v1).
  rewrite div_add_l. 2: lia.
  rewrite div_small; lia.
Qed.

Lemma divpow2r_eq n i:
  n mod 2^(i+1) <> (2^i)-1 ->
  (divpow2r n i) =
  divpow2r (n+1) i.
Proof.
  unfold divpow2r.
  rewrite (Nat.add_comm i 1).
  intro H.
  rewrite (Div0.div_mod n (2 ^ (1+i))).
  remember (n / 2 ^ (1+i)) as v1.
  remember (n mod 2 ^ (1+i)) as v2.
  rewrite (Nat.mul_comm (2^(1+i)) v1).
  repeat rewrite <-Nat.add_assoc.
  rewrite div_add_l. 2: apply pow2_nez.
  rewrite div_add_l. 2: apply pow2_nez.
  assert (E:v2<2^i-1\/2^i<=v2) by lia.
  destruct E as [E|E].
  - rewrite div_small. 2: cbn; lia.
    rewrite div_small. 2: cbn; lia.
    lia.
  - assert (E0:v2=v2-2^i+2^i) by lia.
    rewrite E0.
    remember (v2-2^i) as v3.
    replace (v3 + 2 ^ i + 2 ^ i) with (1 * (2 * 2 ^ i) + v3) by lia.
    change (2*2^i) with (2^(1+i)).
    rewrite div_add_l. 2: apply pow2_nez.
    eassert (E1:_) by apply (mod_upper_bound n (2^(1+i))),pow2_nez.
    rewrite <-Heqv2 in E1. cbn in E1.
    rewrite div_small. 2: cbn; lia.
    replace (v3 + 2 ^ i + (1 + 2 ^ i)) with (1 * (2 * 2 ^ i) + (v3 + 1)) by lia.
    rewrite div_add_l. 2: apply pow2_nez.
    rewrite div_small. 2: cbn; lia.
    reflexivity.
Qed.



Lemma divpow2r_d_lt i n xs:
  i<n ->
  divpow2r (binary_to_nat ((repeat true n) ++ false :: xs)) i =
  divpow2r (binary_to_nat ((repeat false n) ++ true :: xs)) i.
Proof.
  rewrite <-binary_to_nat_S.
  rewrite binary_to_nat_1s_app.
  cbn.
  remember (binary_to_nat xs) as v1.
  intro H.
  rewrite <- (Nat.add_1_r (v1 * 2 * 2 ^ n + 2 ^ n - 1)).
  apply divpow2r_eq.
  replace (v1 * 2 * 2 ^ n + 2 ^ n - 1) with (2^n*(v1*2)+(2^n-1)) by lia.
  replace (2^n) with (2^(i+1) * 2^(n-(i+1))).
  2: {
    rewrite <-pow_add_r.
    f_equal. lia.
  }
  rewrite <-Div0.add_mod_idemp_l.
  rewrite <-Nat.mul_assoc.
  rewrite mul_comm,Div0.mod_mul.
  cbn.
  assert (E:(n - (i + 1) = 0 \/ (n - (i + 1))>0)%nat) by lia.
  destruct E as [E|E].
  - rewrite E.
    cbn.
    pose proof (pow2_nez (i+1)) as E0.
    pose proof (pow2_nez (i)) as E1.
    rewrite mul_1_r,mod_small. 2: lia.
    rewrite add_comm. cbn. lia.
  - pose proof (pow2_nez (i+1)) as E0.
    pose proof (pow2_nez (i)) as E1.
    pose proof (pow2_nez (n-(i+1))) as E2.
    remember (n-(i+1)) as v2.
    replace (2^v2) with (2^v2-1+1) by lia.
    rewrite mul_add_distr_l.
    rewrite <-add_sub_assoc. 2: lia.
    rewrite <-Div0.add_mod_idemp_l.
    rewrite mul_comm,Div0.mod_mul.
    cbn.
    rewrite mul_1_r,mod_small. 2: lia.
    rewrite add_comm.
    cbn. lia.
Qed.


Lemma divpow2r_d_eq n xs:
  S (divpow2r (binary_to_nat ((repeat true n) ++ false :: xs)) n) =
  divpow2r (binary_to_nat ((repeat false n) ++ true :: xs)) n.
Proof.
  rewrite <-binary_to_nat_S.
  rewrite binary_to_nat_1s_app.
  cbn.
  remember (binary_to_nat xs) as v1.
  rewrite <- (Nat.add_1_r (divpow2r (v1 * 2 * 2 ^ n + 2 ^ n - 1) n)).
  rewrite <- (Nat.add_1_r (v1 * 2 * 2 ^ n + 2 ^ n - 1)).
  apply divpow2r_inc.
  rewrite <-mul_assoc.
  change (2*2^n) with (2^(1+n)).
  rewrite (add_comm n 1).
  pose proof (pow2_nez (n)) as E.
  rewrite <-add_sub_assoc. 2: lia.
  rewrite <-Div0.add_mod_idemp_l.
  rewrite Div0.mod_mul.
  rewrite mod_small. 2: cbn; lia.
  reflexivity.
Qed.

Lemma divpow2r_d_gt i n xs:
  n<i ->
  divpow2r (binary_to_nat ((repeat true n) ++ false :: xs)) i =
  divpow2r (binary_to_nat ((repeat false n) ++ true :: xs)) i.
Proof.
  rewrite <-binary_to_nat_S.
  rewrite binary_to_nat_1s_app.
  cbn.
  remember (binary_to_nat xs) as v1.
  intro H.
  rewrite <- (Nat.add_1_r (v1 * 2 * 2 ^ n + 2 ^ n - 1)).
  apply divpow2r_eq.
  rewrite <-mul_assoc.
  change (2*2^n) with (2^(1+n)).
  pose proof (pow2_nez (n)) as E.
  rewrite <-add_sub_assoc. 2: lia.
  rewrite (add_comm 1 n).
  replace (2^(i+1)) with (2^(n+1)*2^(i-n)).
  2: {
    rewrite <-pow_add_r.
    f_equal. lia.
  }
  rewrite <-Div0.add_mod_idemp_l.
  rewrite mul_comm,Div0.mul_mod_distr_l.
  remember (v1 mod 2 ^ (i - n)) as v2.
  replace (2^(i)) with (2^(n)*2^(i-n)).
  2: {
    rewrite <-pow_add_r.
    f_equal. lia.
  }
  rewrite (add_comm n 1).
  change (2^(1+n)) with (2*2^n).
  remember (2^n) as v3.
  assert (E0:(i-n=0\/i-n>0)%nat) by lia.
  destruct E0 as [E0|E0].
  - rewrite E0.
    change (2^0)%nat with 1%nat.
    rewrite mul_1_r.
    rewrite <-Div0.add_mod_idemp_l.
    rewrite mul_comm,Div0.mod_mul.
    rewrite mod_small; lia.
  - rewrite Div0.add_mul_mod_distr_l. 2: lia.
    intro H0.
    pose proof (pow2_nez (i-n)) as E1.
    assert (E2:2 * v3 * (v2 mod 2 ^ (i - n)) + (v3) = v3 * 2 ^ (i - n)) by lia.
    remember (v2 mod 2 ^ (i - n)) as v4.
    replace (i-n) with (1+(i-n-1)) in E2 by lia.
    change (2^(1+(i-n-1))) with (2*(2^(i-n-1))) in E2.
    replace (2 * v3 * v4 + v3) with (v3*(v4*2+1)) in E2 by lia.
    rewrite mul_cancel_l in E2. 2: auto 1.
    lia.
Qed.

(* one induction step of Proposition 2.2 *)
Lemma Increment_a {s1 s2}:
  Increment s1 s2 ->
  if to_s s1 then
  forall i,
    nth i (snd s2) O + divpow2r (to_n s1) i =
    nth i (snd s1) O + divpow2r (to_n s2) i
  else
  forall i,
    nth i (snd s1) O + divpow2r (to_n s1) i =
    nth i (snd s2) O + divpow2r (to_n s2) i.
Proof.
  intro I.
  destruct s1 as [x1 xs1].
  destruct s2 as [x2 xs2].
  destruct (to_s (x1,xs1)) eqn:E.
{
  inverts I.
  - intro i.
    cbn.
    rewrite Increment_inc with (x2:=x2); auto 1.
    rewrite Increment_dec with (x2:=x2); auto 1.
    2: rewrite to_s_S',E; reflexivity.
    remember (S (length xs)) as sl.
    cbn.
    remember (grey_to_binary (map odd zs)) as v1.
    assert (E0:i<sl\/i=sl\/i>sl) by lia.
    assert (E1:length (xs++[y]) = sl). {
      rewrite length_app.
      cbn. lia.
    }
    rewrite app_cons_r.
    symmetry. 
    rewrite app_cons_r.
    destruct E0 as [E0|[E0|E0]].
    + rewrite app_nth1. 2: lia.
      symmetry.
      rewrite app_nth1. 2: lia.
      f_equal.
      apply divpow2r_d_lt,E0.
    + rewrite E0,<-E1.
      do 2 rewrite nth_middle.
      rewrite E1.
      rewrite <-divpow2r_d_eq.
      lia.
    + rewrite app_cons_r.
      symmetry. 
      rewrite app_cons_r.
      assert (E2:length ((xs ++ [y]) ++ [S z])=S sl) by (rewrite length_app; cbn; lia).
      assert (E3:length ((xs ++ [y]) ++ [z])=S sl) by (rewrite length_app; cbn; lia).
      rewrite app_nth2. 2: lia.
      rewrite app_nth2. 2: lia.
      rewrite E2,E3.
      f_equal.
      apply divpow2r_d_gt. lia.
  - intro i.
    unfold to_n,to_n_binary,snd,list_to_binary.
    rewrite Increment_inc_odd with (x2:=x2); auto 1.
    rewrite Increment_dec_odd with (x2:=x2); auto 1.
    2: rewrite to_s_S_odd,E; reflexivity.
    destruct i as [|i].
    + cbn[nth].
      pose proof (divpow2r_d_eq O).
      cbn[repeat] in H.
      cbn[app] in H.
      rewrite <-H.
      lia.
    + cbn[nth].
      f_equal.
      pose proof (divpow2r_d_gt (S i) O).
      cbn[repeat] in H.
      cbn[app] in H.
      rewrite <-H. 2: lia.
      reflexivity.
}
{
  inverts I.
  - intro i.
    cbn.
    rewrite Increment_dec with (x2:=x2); auto 1.
    rewrite Increment_inc with (x2:=x2); auto 1.
    2: rewrite to_s_S',E; reflexivity.
    remember (S (length xs)) as sl.
    cbn.
    remember (grey_to_binary (map odd zs)) as v1.
    assert (E0:i<sl\/i=sl\/i>sl) by lia.
    assert (E1:length (xs++[y]) = sl). {
      rewrite length_app.
      cbn. lia.
    }
    rewrite app_cons_r.
    symmetry. 
    rewrite app_cons_r.
    destruct E0 as [E0|[E0|E0]].
    + rewrite app_nth1. 2: lia.
      symmetry.
      rewrite app_nth1. 2: lia.
      f_equal. symmetry.
      apply divpow2r_d_lt,E0.
    + rewrite E0,<-E1.
      do 2 rewrite nth_middle.
      rewrite E1.
      rewrite <-divpow2r_d_eq.
      lia.
    + rewrite app_cons_r.
      symmetry. 
      rewrite app_cons_r.
      assert (E2:length ((xs ++ [y]) ++ [S z])=S sl) by (rewrite length_app; cbn; lia).
      assert (E3:length ((xs ++ [y]) ++ [z])=S sl) by (rewrite length_app; cbn; lia).
      rewrite app_nth2. 2: lia.
      rewrite app_nth2. 2: lia.
      rewrite E2,E3.
      f_equal. symmetry.
      apply divpow2r_d_gt. lia.
  - intro i.
    unfold to_n,to_n_binary,snd,list_to_binary.
    rewrite Increment_dec_odd with (x2:=x2); auto 1.
    rewrite Increment_inc_odd with (x2:=x2); auto 1.
    2: rewrite to_s_S_odd,E; reflexivity.
    destruct i as [|i].
    + cbn[nth].
      pose proof (divpow2r_d_eq O).
      cbn[repeat] in H.
      cbn[app] in H.
      rewrite <-H.
      lia.
    + cbn[nth].
      f_equal.
      pose proof (divpow2r_d_gt (S i) O).
      cbn[repeat] in H.
      cbn[app] in H.
      rewrite <-H. 2: lia.
      reflexivity.
}
Qed.


Definition ai(i:nat)(s:nat*(list nat)) :=
  nth i (snd s) O.

Inductive Increments: nat->(nat*(list nat))->(nat*(list nat))->Prop :=
| Increments_O s: Increments O s s
| Increments_S n s1 s2 s3:
  Increment s1 s2 ->
  Increments n s2 s3 ->
  Increments (S n) s1 s3
.

(* Proposition 2.2 (i>=1) *)
Lemma Increments_a {n s1 s2}:
  Increments n s1 s2 ->
  if to_s s1 then
  forall i,
    ai i s2 + divpow2r (to_n s1) i =
    ai i s1 + divpow2r (to_n s2) i
  else
  forall i,
    ai i s1 + divpow2r (to_n s1) i =
    ai i s2 + divpow2r (to_n s2) i.
Proof.
  unfold ai.
  intro I.
  induction I.
  1: destruct (to_s s); reflexivity.
  pose proof (Increment_a H) as Hd.
  rewrite <-(Increment_sgn H) in IHI.
  pose proof (Increment_n H) as Hn.
  destruct (to_s s2) eqn:E;
    intro i;
    specialize (IHI i);
    specialize (Hd i);
    lia.
Qed.

(* Proposition 2.2 (i=0) *)
Lemma Increments_a0 {n s1 s2}:
  Increments n s1 s2 ->
  if to_s s1 then
    (fst s1) + (to_n s1) =
    (fst s2) + (to_n s2)
  else
    (fst s2) + (to_n s1) =
    (fst s1) + (to_n s2).
Proof.
  intro I.
  induction I.
  1: destruct (to_s s); reflexivity.
  rewrite <-(Increment_sgn H) in IHI.
  pose proof (Increment_n H) as Hn.
  destruct (to_s s2) eqn:E;
    inverts H;
      destruct s4 as [x4 xs4];
      unfold fst;
      unfold fst in IHI;
      lia.
Qed.

Lemma Increment_a0 {s1 s2}:
  Increment s1 s2 ->
  if to_s s1 then
    (fst s1) + (to_n s1) =
    (fst s2) + (to_n s2)
  else
    (fst s2) + (to_n s1) =
    (fst s1) + (to_n s2).
Proof.
  intros.
  eapply (Increments_a0).
  econstructor; eauto 1; constructor.
Qed.




(* some trivial lemmas *)
Lemma Forall_Even_dec xs:
  Forall Even xs \/
  exists xs0 y zs,
    Forall Even xs0 /\
    Odd y /\
    xs = xs0 ++ y :: zs.
Proof.
  induction xs.
  - left. auto 1.
  - destruct IHxs as [IHxs|[xs0 [y [zs [H0 [H1 H2]]]]]].
    + destruct (Even_or_Odd a) as [H|H].
      * left. auto 2.
      * right.
        exists (@nil nat) a xs.
        repeat split; auto 1.
    + right.
      destruct (Even_or_Odd a) as [H|H].
      * exists (a::xs0) y zs.
        repeat split; auto 1.
        -- constructor; auto 1.
        -- cbn. congruence.
      * exists (@nil nat) a xs.
        repeat split; auto 1.
Qed.

Lemma to_n_Even x xs:
  Forall Even xs ->
  to_n (x,xs) = O.
Proof.
  intro H.
  cbn.
  replace ((grey_to_binary (map odd xs))) with (repeat false (length xs)). 2:{
    induction xs.
    1: reflexivity.
    inverts H.
    cbn.
    rewrite <-IHxs; auto 1.
    f_equal.
    unfold odd.
    OE_oe. rewrite H2.
    cbn.
    destruct xs; reflexivity.
  }
  apply binary_to_nat_0s.
Qed.

Lemma to_n_0_binary_0_Even x xs:
  to_n (x, xs) = O ->
  (grey_to_binary (map odd xs)) = repeat false (length xs) /\
  Forall Even xs.
Proof.
  unfold to_n. cbn.
  induction xs.
  1: intro; split; [reflexivity | constructor ].
  intro H.
  cbn in H.
  rewrite eq_add_0 in H.
  destruct H as [X1 X2].
  rewrite eq_mul_0 in X2.
  destruct X2 as [X2|X2]. 2: congruence.
  specialize (IHxs X2).
  destruct IHxs as [I1 I2].
  cbn.
  rewrite I1.
  rewrite I1 in X1.
  assert (E1:hd false (repeat false (length xs)) = false)
    by (destruct xs; reflexivity).
  rewrite E1 in X1.
  destruct (odd a) eqn:E; cbn in X1.
  1: congruence.
  cbn.
  simpl_xor_neg.
  rewrite E1.
  split; auto 1.
  constructor; auto 1.
  unfold odd in E.
  rewrite <-even_spec.
  destruct (even a); cbn in E; congruence.
Qed.

Lemma to_n_0_Even x xs:
  to_n (x, xs) = O ->
  Forall Even xs.
Proof.
  intro H.
  apply (to_n_0_binary_0_Even _ _ H).
Qed.



Inductive WF1: (nat*(list nat))->Prop :=
| WF1_intro x xs y:
  Forall Nonzero xs ->
  WF1 (x,xs ++ [y]).

Inductive WF2: (nat*(list nat))->Prop :=
| WF2_intro x xs y zs:
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  Forall Nonzero zs ->
  WF2 (x,xs ++ y :: zs ++ [O; O])
.

(* weak pre-cond for Inc/Halve/Zero/Overflow *)
Inductive WF: (nat*(list nat))->Prop :=
| WF_1 s:
  WF1 s -> WF s
| WF_2 s:
  WF2 s -> WF s
.

Lemma WF1_00 x xs:
  ~WF1 (x, xs ++ [0; 0]%nat).
Proof.
  intro H.
  inverts H.
  rewrite (app_cons_r xs) in H2.
  rewrite app_inj_tail_iff in H2.
  destruct H2 as [H3 H4].
  rewrite H3 in H1.
  rewrite Forall_app in H1.
  destruct H1 as [_ H].
  inverts H.
  lia.
Qed.


Lemma WF_nonempty {x xs}:
  WF (x,xs) ->
  xs<>nil.
Proof.
  intro H.
  inverts H as H; inverts H;
    eapply app_nonempty_r; eauto 1.
Qed.



(* some trivial lemmas *)
Lemma pow2_1a n:
  2^(1+n) = 2*(2^n).
Proof.
  reflexivity.
Qed.

Ltac Odd_Even_contra:=
  match goal with
  | H1:Odd ?x, H2:Even ?x |- _ => destruct (Even_Odd_False _ H2 H1)
  end.

Lemma to_n_pow2sub1 x xs y:
  to_n (x,xs++[y;0;0]%nat) = 2^(to_l (x,xs++[y;0;0]%nat) - 2) - 1 ->
  (hd false (grey_to_binary (map odd (xs++[y;0;0]%nat)))) = true /\
  Forall Even xs /\
  Odd y.
Proof.
  cbn.
  induction xs.
  - cbn.
    destruct (odd y) eqn:Oy; cbn.
    2: congruence.
    rewrite <-odd_spec.
    intro. repeat split; auto 1.
  - cbn.
    cbn in IHxs.
    remember (hd false (grey_to_binary (map odd (xs++[y;0;0]%nat)))) as v1.
    remember (binary_to_nat (grey_to_binary (map odd (xs++[y;0;0]%nat)))) as v2.
    intro H.
    rewrite grey_to_binary_length,length_map,length_app in H,IHxs.
    cbn in H,IHxs.
    replace (length xs + 3 - 1) with (1+(length xs + 3 - 2)) in H by lia.
    rewrite pow2_1a in H.
    pose proof (pow2_nez (length xs + 3 - 2)).
    destruct (xorb (odd a) v1) eqn:E.
    2: lia.
    assert (Hv2:v2 = 2 ^ (length xs + 3 - 2) - 1) by lia.
    specialize (IHxs Hv2).
    destruct IHxs as [I1 [I2 I3]].
    rewrite I1 in E.
    destruct (odd a) eqn:Oa.
    1: cbn in E; congruence.
    unfold odd in Oa.
    generalize Oa. clear Oa.
    simpl_xor_neg.
    intro Ea.
    repeat split; auto 1.
    constructor; auto 1.
    rewrite <-even_spec.
    apply Ea.
Qed.

Lemma WF2_n_lt {s1}:
  WF2 s1 ->
  to_n s1 < 2^(to_l s1 - 2).
Proof.
  intro H.
  inverts H.
  cbn.
  rewrite grey_to_binary_length,length_map.
  replace (xs ++ y :: zs ++ [0; 0]%nat) with
  ((xs ++ y :: zs) ++ [0; 0]%nat).
  2: rewrite <-app_assoc; reflexivity.
  generalize (xs++y::zs).
  clear x xs y zs H0 H1 H2 H3.
  intro l.
  induction l.
  1: cbn; lia.
  cbn.
  remember (grey_to_binary (map odd (l ++ [0; 0]%nat))) as v1.
  generalize IHl; clear IHl.
  rewrite length_app.
  cbn.
  replace (length l + 2 - 1) with (1+(length l + 2 - 2)) by lia.
  rewrite pow2_1a.
  destruct (xorb (odd a) (hd false v1)); lia.
Qed.






(* more pre-cond to keep post-cond also WF;
   also track the transition between WF1,WF2 *)
Lemma Increment_inc_precond1 {s1}:
  WF1 s1 ->
  to_s s1 = true ->
  to_n s1 < 2^(to_l s1) - 1 ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF1 s2.
Proof.
  intros.
  destruct s1 as [x1 xs1].
  cbn in H2.
  destruct x1 as [|x1]. 1: lia.
  destruct (Even_or_Odd x1) as [Ex1|Ox1].
  - inverts H.
      destruct (Forall_Even_dec xs) as [H0'|[xs0 [y0 [zs [H0' [H1' H2']]]]]].
      {
        generalize H0; clear H0.
        unfold to_s.
        simpl_oe_S.
        OE_oe.
        unfold odd. rewrite Ex1.
        cbn.
        simpl_list_to_binary_0s.
        destruct (odd y) eqn:E.
        2: cbn; intro X; congruence.
        intro X. clear X.
        generalize H1; clear H1.
        unfold to_n,to_n_binary,snd.
        simpl_list_to_binary_0s.
        rewrite E. cbn.
        rewrite (grey_to_binary_length),length_map,length_app.
        rewrite repeat_app_S,app_nil_r.
        rewrite binary_to_nat_1s,Nat.add_comm. cbn.
        intro. lia.
      }
      {
        rewrite H2',<-app_assoc. cbn.
        destruct zs; cbn.
        - eexists.
          split.
          + eapply Increment_even; eauto 1.
            rewrite H2' in H4.
            rewrite Forall_app in H4.
            apply H4.
          + rewrite app_cons_r.
            constructor.
            rewrite <-H2'. apply H4.
        - eexists.
          split.
          + eapply Increment_even; eauto 1.
            rewrite H2' in H4.
            rewrite Forall_app in H4.
            apply H4.
          + applys_eq WF1_intro.
            * f_equal.
              do 2 rewrite app_cons_r.
              rewrite app_assoc.
              f_equal.
            * do 2 rewrite <-app_assoc.
              repeat rewrite Forall_app.
              rewrite H2' in H4.
              do 2 rewrite app_cons_r in H4.
              repeat rewrite Forall_app in H4.
              destruct H4 as [[[H4a H4b] H4c] H4d].
              repeat split; auto 1. 
              repeat constructor. lia.
      }
  - destruct xs1 as [|x2 xs1].
    1: pose proof (WF_nonempty (WF_1 _ H)); congruence.
    assert (I12:Increment (S x1, x2 :: xs1) (x1, S x2 :: xs1)).
    { eapply Increment_odd; eauto 1. }
    pose proof (Increment_n I12) as I12n.
    rewrite H0 in I12n.
    eexists.
    split. 1: apply I12.
    destruct x1.
    1: inverts Ox1; lia.
    rewrite Odd_succ in Ox1.
    inverts H.
    {
      destruct xs.
      - cbn in H5.
        inverts H5.
        apply (WF1_intro (S x1) []),H4.
      - cbn in H5.
        inverts H5.
        rewrite app_comm_cons.
        apply WF1_intro.
        inverts H4.
        constructor; auto 1; lia.
    }
Qed.

Lemma Increment_inc_precond22 {s1}:
  WF2 s1 ->
  to_s s1 = true ->
  to_n s1 < 2^(to_l s1 - 2) - 1 ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF2 s2.
Proof.
  intros.
  destruct s1 as [x1 xs1].
  cbn in H2.
  destruct x1 as [|x1]. 1: lia.
  destruct (Even_or_Odd x1) as [Ex1|Ox1].
  - inverts H.
      destruct zs.
      * eassert (I:Increment (S x1, xs ++ y :: [] ++ [0; 0]%nat) _).
        { eapply Increment_even; eauto 1. }
        pose proof (Increment_n I) as Hn.
        rewrite H0 in Hn.
        remember (to_n (S x1, xs ++ y :: [] ++ [0; 0]%nat)) as v1.
        generalize Hn.
        cbn.
        simpl_list_to_binary_0s.
        OE_oe.
        rewrite H7.
        cbn.
        rewrite repeat_app_S.
        rewrite binary_to_nat_0s_app.
        change (binary_to_nat [true; false]) with 1%nat.
        unfold to_l in H1.
        cbn in H1.
        rewrite grey_to_binary_length,length_map,length_app in H1.
        cbn in H1.
        replace (length xs + 3 - 2) with (S (length xs)) in H1 by lia.
        intro H1'.
        lia.
      * eexists.
        split.
        1: cbn; eapply Increment_even; eauto 1.
        applys_eq WF2_intro.
        1: do 3 f_equal; rewrite app_comm_cons; f_equal.
        all: auto 1.
        inverts H8.
        constructor; auto 1; lia.
  - destruct xs1 as [|x2 xs1].
    1: pose proof (WF_nonempty (WF_2 _ H)); congruence.
    assert (I12:Increment (S x1, x2 :: xs1) (x1, S x2 :: xs1)).
    { eapply Increment_odd; eauto 1. }
    pose proof (Increment_n I12) as I12n.
    rewrite H0 in I12n.
    eexists.
    split. 1: apply I12.
    destruct x1.
    1: inverts Ox1; lia.
    rewrite Odd_succ in Ox1.
    inverts H.
    {
      destruct xs.
      - cbn in H4.
        inverts H4.
        rewrite <-Even_succ in H7.
        destruct (Forall_Even_dec zs) as [E|E].
        + assert (Ev:Forall Even (S x2 :: zs ++ [0; 0]%nat)).
          {
            rewrite app_comm_cons.
            rewrite Forall_app.
            split.
            1: constructor; auto 1.
            repeat constructor;
            rewrite <-even_spec; reflexivity.
          }
          rewrite (to_n_Even (S x1) _ Ev) in I12n.
          inverts I12n.
        + destruct E as [xs0 [y [zs0 [E0 [E1 E2]]]]].
          subst zs.
          rewrite app_cons_r in H8.
          repeat rewrite Forall_app in H8.
          destruct H8 as [[H8a H8b] H8c].
          applys_eq (WF2_intro (S x1) (S x2::xs0) y zs0).
          1: f_equal; cbn; rewrite <-app_assoc; reflexivity.
          all: try constructor; auto 1; lia.
      - cbn in H4. inverts H4.
        inverts H6. inverts H5.
        rewrite <-Odd_succ in H4.
        applys_eq (WF2_intro (S x1) nil (S x2) (xs++y::zs)).
        1: rewrite <-app_assoc; reflexivity.
        all: auto 1.
        rewrite Forall_app. split; auto 1.
        constructor; auto 1.
        intro X. subst. OE_oe. cbn in H7. congruence.
    }
Qed.



Lemma Increment_inc_precond21 {s1}:
  WF2 s1 ->
  to_s s1 = true ->
  to_n s1 = 2^(to_l s1 - 2) - 1 ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF1 s2.
Proof.
  intros.
  destruct s1 as [x1 xs1].
  cbn in H2.
  destruct x1 as [|x1]. 1: lia.
  inverts H.
  destruct zs.
  - cbn[app] in H1.
    destruct (to_n_pow2sub1 _ _ _ H1) as [I1 [I2 I3]].
    generalize H0; clear H0.  
    unfold to_s.
    simpl_oe_S. cbn.
    unfold list_to_binary.
    rewrite I1.
    destruct (odd x1) eqn:Ox1; cbn; intro X.
    1: congruence.
    unfold odd in Ox1.
    rewrite Bool.negb_false_iff in Ox1.
    rewrite even_spec in Ox1.
    eexists.
    split.
    + eapply Increment_even; eauto 1.
    + do 2 rewrite app_cons_r.
      apply WF1_intro.
      repeat rewrite Forall_app.
      destruct y. 1: inverts I3; lia.
      repeat split; auto 1; repeat constructor; lia.
  - assert (H:n::zs<>[]) by congruence.
    destruct (exists_last H) as [zs0 [y0 H']].
    rewrite H' in H1.
    replace (xs ++ y :: (zs0 ++ [y0]) ++ [0; 0]%nat) with
    ((xs++y::zs0)++[y0;0;0]%nat) in H1.
    2: {
      do 2 rewrite <-app_assoc.
      reflexivity.
    }
    destruct (to_n_pow2sub1 _ _ _ H1) as [I1 [I2 I3]].
    rewrite Forall_app in I2.
    inverts I2. inverts H4.
    Odd_Even_contra.
Qed.


Lemma Increment_dec_precond1 {s1}:
  WF1 s1 ->
  to_s s1 = false ->
  to_n s1 > O ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF1 s2.
Proof.
  intros.
  destruct s1 as [x1 xs1].
  cbn in H2.
  destruct x1 as [|x1]. 1: lia.
  destruct (Even_or_Odd x1) as [Ex1|Ox1].
  - inverts H.
    + destruct (Forall_Even_dec xs) as [H0'|[xs0 [y0 [zs [H0' [H1' H2']]]]]].
      {
        generalize H0; clear H0.
        unfold to_s.
        simpl_oe_S.
        OE_oe.
        unfold odd. rewrite Ex1.
        cbn.
        simpl_list_to_binary_0s.
        destruct (odd y) eqn:E.
        1: cbn; intro X; congruence.
        intro X. clear X.
        generalize H1; clear H1.
        unfold to_n,to_n_binary,snd.
        simpl_list_to_binary_0s.
        rewrite E. cbn.
        rewrite repeat_app_S,app_nil_r.
        rewrite binary_to_nat_0s.
        intro. lia.
      }
      {
        rewrite H2',<-app_assoc. cbn.
        destruct zs; cbn.
        - eexists.
          split.
          + eapply Increment_even; eauto 1.
            rewrite H2' in H4.
            rewrite Forall_app in H4.
            apply H4.
          + rewrite app_cons_r.
            apply WF1_intro.
            rewrite <-H2'. apply H4.
        - eexists.
          split.
          + eapply Increment_even; eauto 1.
            rewrite H2' in H4.
            rewrite Forall_app in H4.
            apply H4.
          + applys_eq WF1_intro.
            * f_equal.
              do 2 rewrite app_cons_r.
              rewrite app_assoc.
              f_equal.
            * do 2 rewrite <-app_assoc.
              repeat rewrite Forall_app.
              rewrite H2' in H4.
              do 2 rewrite app_cons_r in H4.
              repeat rewrite Forall_app in H4.
              destruct H4 as [[[H4a H4b] H4c] H4d].
              repeat split; auto 1. 
              repeat constructor. lia.
      }
  - destruct xs1 as [|x2 xs1].
    1: pose proof (WF_nonempty (WF_1 _ H)); congruence.
    assert (I12:Increment (S x1, x2 :: xs1) (x1, S x2 :: xs1)).
    { eapply Increment_odd; eauto 1. }
    pose proof (Increment_n I12) as I12n.
    rewrite H0 in I12n.
    eexists.
    split. 1: apply I12.
    destruct x1.
    1: inverts Ox1; lia.
    rewrite Odd_succ in Ox1.
    inverts H.
    {
      destruct xs.
      - cbn in H5.
        inverts H5.
        apply (WF1_intro (S x1) []),H4.
      - cbn in H5.
        inverts H5.
        rewrite app_comm_cons.
        apply WF1_intro.
        inverts H4.
        constructor; auto 1; lia.
    }
Qed.

Lemma Increment_dec_precond2 {s1}:
  WF2 s1 ->
  to_s s1 = false ->
  to_n s1 > S O ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF2 s2.
Proof.
  intros.
  destruct s1 as [x1 xs1].
  cbn in H2.
  destruct x1 as [|x1]. 1: lia.
  destruct (Even_or_Odd x1) as [Ex1|Ox1].
  - inverts H.
    + destruct zs.
      * generalize H0.
        unfold to_s.
        OE_oe.
        simpl_oe_S.
        unfold odd.
        rewrite Ex1.
        cbn.
        simpl_list_to_binary_0s.
        rewrite H7.
        cbn; intro; congruence.
      * eexists.
        split.
        1: cbn; eapply Increment_even; eauto 1.
        applys_eq WF2_intro.
        1: do 3 f_equal; rewrite app_comm_cons; f_equal.
        all: auto 1.
        inverts H8.
        constructor; auto 1; lia.
  - destruct xs1 as [|x2 xs1].
    1: pose proof (WF_nonempty (WF_2 _ H)); congruence.
    assert (I12:Increment (S x1, x2 :: xs1) (x1, S x2 :: xs1)).
    { eapply Increment_odd; eauto 1. }
    pose proof (Increment_n I12) as I12n.
    rewrite H0 in I12n.
    eexists.
    split. 1: apply I12.
    destruct x1.
    1: inverts Ox1; lia.
    rewrite Odd_succ in Ox1.
    inverts H.
    {
      destruct xs.
      - cbn in H4.
        inverts H4.
        rewrite <-Even_succ in H7.
        destruct (Forall_Even_dec zs) as [E|E].
        + assert (Ev:Forall Even (S x2 :: zs ++ [0; 0]%nat)).
          {
            rewrite app_comm_cons.
            rewrite Forall_app.
            split.
            1: constructor; auto 1.
            repeat constructor;
            rewrite <-even_spec; reflexivity.
          }
          rewrite (to_n_Even (S x1) _ Ev) in I12n.
          lia.
        + destruct E as [xs0 [y [zs0 [E0 [E1 E2]]]]].
          subst zs.
          rewrite app_cons_r in H8.
          repeat rewrite Forall_app in H8.
          destruct H8 as [[H8a H8b] H8c].
          applys_eq (WF2_intro (S x1) (S x2::xs0) y zs0).
          1: f_equal; cbn; rewrite <-app_assoc; reflexivity.
          all: try constructor; auto 1; lia.
      - cbn in H4. inverts H4.
        inverts H6. inverts H5.
        rewrite <-Odd_succ in H4.
        applys_eq (WF2_intro (S x1) nil (S x2) (xs++y::zs)).
        1: rewrite <-app_assoc; reflexivity.
        all: auto 1.
        rewrite Forall_app. split; auto 1.
        constructor; auto 1.
        intro X. subst. OE_oe. cbn in H7. congruence.
    }
Qed.

Lemma Halve_precond1 {s1}:
  WF1 s1 ->
  fst s1 = O ->
  to_l s1 >= 2 ->
  exists s2, Halve s1 s2 /\ WF1 s2.
Proof.
  destruct s1 as [x xs].
  cbn.
  intros.
  rename H1 into H1'.
  subst.
  inverts H.
  destruct xs0.
  + cbn.
    eexists.
    split.
    1: econstructor.
    rewrite grey_to_binary_length,length_map in H1'.
    cbn in H1'. lia.
  + cbn.
    eexists.
    split.
    1: econstructor.
    inverts H1.
    apply WF1_intro; auto 2.
Qed.

Lemma Halve_precond2 {s1}:
  WF2 s1 ->
  fst s1 = O ->
  (to_n s1 <> S O) ->
  exists s2, Halve s1 s2 /\ WF2 s2.
Proof.
  destruct s1 as [x xs].
  cbn.
  intros.
  rename H1 into H2'.
  subst.
  inverts H.
    destruct xs0.
    + cbn.
      eexists.
      split.
      1: econstructor.
      destruct (Forall_Even_dec zs) as [E|E].
      * generalize H2'; clear H2'.
        cbn.
        simpl_list_to_binary_0s.
        OE_oe.
        rewrite H4.
        cbn.
        rewrite binary_to_nat_0s_app.
        cbn. lia.
      * destruct E as [xs0 [y0 [zs0 [E0 [E1 E2]]]]].
        subst zs.
        rewrite Forall_app in H5.
        destruct H5 as [H5a H5b].
        inverts H5b.
        applys_eq WF2_intro.
        1: rewrite <-app_assoc; cbn; reflexivity.
        all: auto 1.
    + cbn.
      eexists.
      split.
      1: econstructor.
      inverts H2. inverts H3.
      apply WF2_intro; auto 1.
Qed.

Lemma dec_to_0__a0_Odd {s1}:
  to_s s1 = false ->
  to_n s1 = O ->
  Odd (fst s1).
Proof.
  destruct s1 as [x xs].
  intros.
  destruct (to_n_0_binary_0_Even _ _ H0).
  cbn.
  cbn in H.
  unfold list_to_binary in H.
  rewrite H1 in H.
  rewrite <-odd_spec.
  unfold odd.
  generalize H; clear H.
  destruct xs; cbn;
  simpl_xor_neg;
  destruct (even x); cbn; congruence.
Qed.

Lemma Zero_precond {s1}:
  WF1 s1 ->
  to_s s1 = false ->
  to_n s1 = O ->
  exists s2, Zero s1 s2 /\ WF2 s2.
Proof.
  intros.
  pose proof (dec_to_0__a0_Odd H0 H1).
  inverts H.
  pose proof (to_n_0_Even _ _ H1) as Ev.
  rewrite Forall_app in Ev.
  destruct Ev as [Ev1 Ev2].
  cbn in H2.
  destruct x as [|x]. 1: inverts H2; lia.
  rewrite Odd_succ in H2.
  inverts Ev2.
  eexists.
  split.
  1: constructor; auto 1.
  apply (WF2_intro x xs (S y) nil); auto 1.
  rewrite Odd_succ.
  apply H5.
Qed.


Ltac rsplit :=
  try match goal with
  | |- (?a /\ ?b) => split; rsplit
  end.

Lemma Overflow_precond_0 x xs y:
  to_n (x,xs++[y]) = 2^(to_l (x,xs++[y]))-1 ->
  hd false (grey_to_binary (map odd (xs ++ [y]))) = true /\
  Forall Even xs /\ Odd y.
Proof.
  induction xs.
  - cbn.
    destruct (odd y) eqn:Ey; cbn.
    2: congruence.
    intros.
    rsplit; auto 1.
    rewrite <-odd_spec.
    apply Ey.
  - gen IHxs.
    cbn.
    remember (grey_to_binary (map odd (xs ++ [y]))) as v1.
    remember (xorb (odd a) (hd false v1)) as v2.
    intro IHxs.
    pose proof (pow2_nez (length v1)).
    destruct v2; cbn. 2: lia.
    intro H0.
    eassert _ as X by (apply IHxs; lia).
    destruct X as [X1 [X2 X3]].
    rsplit; auto 1.
    constructor; auto 1.
    rewrite <-even_spec.
    rewrite X1 in Heqv2.
    unfold odd in Heqv2.
    destruct (even a) eqn:Ea; cbn in Heqv2; congruence.
Qed.

Close Scope sym_scope.
Lemma Overflow_precond {s1}:
  WF1 s1 ->
  to_s s1 = true ->
  to_n s1 = 2^(to_l s1) - 1 ->
  fst s1 = 1 ->
  exists s2, Overflow s1 s2 /\ WF1 s2.
Proof.
  intros.
  inverts H.
  pose proof (Overflow_precond_0 x xs y H1) as H4.
  destruct H4 as [H4 [H5 H6]].
  cbn in H2.
  subst.
  eexists.
  split.
  1: econstructor; eauto 1.
  rewrite app_cons_r.
  econstructor.
  rewrite Forall_app.
  split; auto 2.
Qed.

Lemma Increments_inc_precond1 {s1} n:
  WF1 s1 ->
  to_s s1 = true ->
  to_n s1 + n < 2^(to_l s1) ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF1 s2.
Proof.
  gen s1.
  induction n.
  - intros. eexists.
    split. 1: constructor.
    auto 1.
  - intros.
    eassert (I:_) by
      (eapply Increment_inc_precond1; eauto 1; lia).
    destruct I as [s4 [I1 I2]].
    pose proof (Increment_n I1) as Hn.
    pose proof (Increment_sgn I1) as Hs.
    pose proof (Increment_len I1) as Hl.
    pose proof (Increment_a0 I1) as Hd.
    rewrite H0 in Hn,Hd.
    eassert (X:_). {
      apply IHn.
      - apply I2.
      - rewrite <-Hs. apply H0.
      - pose proof (pow2_nez (to_l s4)).
        rewrite Hl in H1.
        lia.
      - lia.
    }
    destruct X as [s3 [X1 X2]].
    eexists s3.
    split.
    + econstructor; eauto 1.  
    + auto 1.
Qed.

Lemma Increments_inc_precond2 {s1} n:
  WF2 s1 ->
  to_s s1 = true ->
  to_n s1 + n >= 2^(to_l s1 - 2) ->
  to_n s1 + n < 2^(to_l s1) ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF1 s2.
Proof.
  gen s1.
  induction n.
  - intros.
    pose proof (WF2_n_lt H); lia.
  - intros.
    pose proof (WF2_n_lt H) as Hlt.
    assert (Hle:to_n s2 < 2^(to_l s2 - 2) - 1 \/ to_n s2 = 2^(to_l s2 - 2) - 1) by lia.
    clear Hlt.
    destruct Hle as [Hlt|Heq].
    + eassert (I:_) by
        (eapply Increment_inc_precond22; eauto 1; lia).
      destruct I as [s4 [I1 I2]].
      pose proof (Increment_n I1) as Hn.
      pose proof (Increment_sgn I1) as Hs.
      pose proof (Increment_len I1) as Hl.
      pose proof (Increment_a0 I1) as Hd.
      rewrite H0 in Hn,Hd. rewrite Hl in H2.
      eassert (X:_). {
        apply IHn.
        - apply I2.
        - rewrite <-Hs. apply H0.
        - pose proof (pow2_nez (to_l s4)).
          rewrite Hl in H1.
          lia.
        - lia.
        - lia.
      }
      destruct X as [s3 [X1 X2]].
      eexists s3.
      split.
      * econstructor; eauto 1.
      * auto 1.
    + eassert (I:_) by
        (eapply Increment_inc_precond21; eauto 1; lia).
      destruct I as [s4 [I1 I2]].
      pose proof (Increment_n I1) as Hn.
      pose proof (Increment_sgn I1) as Hs.
      pose proof (Increment_len I1) as Hl.
      pose proof (Increment_a0 I1) as Hd.
      rewrite H0 in Hn,Hd. rewrite Hl in H2.
      eassert (X:_). {
        eapply Increments_inc_precond1 with (n:=n).
        - apply I2.
        - rewrite <-Hs. apply H0.
        - pose proof (pow2_nez (to_l s4)).
          rewrite Hl in H1.
          lia.
        - lia.
      }
      destruct X as [s3 [X1 X2]].
      eexists s3.
      split.
      * econstructor; eauto 1.
      * auto 1.
Qed.

Lemma Increments_dec_precond1 {s1} n:
  WF1 s1 ->
  to_s s1 = false ->
  to_n s1 >= n ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF1 s2.
Proof.
  gen s1.
  induction n.
  - intros. eexists.
    split. 1: constructor.
    auto 1.
  - intros.
    eassert (I:_) by
      (eapply Increment_dec_precond1; eauto 1; lia).
    destruct I as [s4 [I1 I2]].
    pose proof (Increment_n I1) as Hn.
    pose proof (Increment_sgn I1) as Hs.
    pose proof (Increment_len I1) as Hl.
    pose proof (Increment_a0 I1) as Hd.
    rewrite H0 in Hn,Hd.
    eassert (X:_). {
      apply IHn.
      - apply I2.
      - rewrite <-Hs. apply H0.
      - inverts I1; lia.
      - lia.
    }
    destruct X as [s3 [X1 X2]].
    eexists s3.
    split.
    + econstructor; eauto 1.  
    + auto 1.
Qed.

Lemma Increments_dec_precond2 {s1} n:
  WF2 s1 ->
  to_s s1 = false ->
  to_n s1 >= S n ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF2 s2.
Proof.
  gen s1.
  induction n.
  - intros. eexists.
    split. 1: constructor.
    auto 1.
  - intros.
    eassert (I:_) by
      (eapply Increment_dec_precond2; eauto 1; lia).
    destruct I as [s4 [I1 I2]].
    pose proof (Increment_n I1) as Hn.
    pose proof (Increment_sgn I1) as Hs.
    pose proof (Increment_len I1) as Hl.
    pose proof (Increment_a0 I1) as Hd.
    rewrite H0 in Hn,Hd.
    eassert (X:_). {
      apply IHn.
      - apply I2.
      - rewrite <-Hs. apply H0.
      - inverts I1; lia.
      - lia.
    }
    destruct X as [s3 [X1 X2]].
    eexists s3.
    split.
    + econstructor; eauto 1.
    + auto 1.
Qed.

Inductive Box(P:Prop):Prop :=
| Box_intro: P -> Box P
.

Inductive weakly_embanked: (nat*(list nat))->(nat*(list nat))->nat->nat->nat->nat->Prop :=
| weakly_embanked_intro n1' n2' s1' s2' s3' s4' s5' s6'
  (* use ' to avoid auto-renaming of number suffix in the name *)
  (Z12':Zero s1' s2')
  (I23':Increments n1' s2' s3')
  (H34':Halve s3' s4')
  (I45':Increments (S n2') s4' s5')
  (H56':Halve s5' s6')

  (Hwf1':WF1 s1')
  (Hs1s:to_s s1' = false)
  (Hs1n:to_n s1' = O)
  (Hs1l:to_l s1' >= 3)
  (Hs1a0_odd:Odd (fst s1'))
  (Hs1a0_lt:fst s1' < 2 ^ to_l s1' - 1)
  (Hs1a1_lt:ai O s1' < 3 * (2 ^ (to_l s1' - 1)))

  (Hwf6':WF1 s6')
  (Hs6s:to_s s6' = false)
  (Hs6l:to_l s6' = to_l s1')

  (* use Box to avoid subst to use this equations *)
  (n34_expr:Box ((to_n s4') = (to_n s3')/2))
  (n56_expr:Box ((to_n s6') = (to_n s5')/2))

  (n3_expr:(to_n s3') + (fst s1') = 2^(to_l s1'))
  (n4_expr:(to_n s4') + (fst s1')/2 + 1 = 2^(to_l s1' - 1))
  (n5_expr:(to_n s5') = (ai O s1') + 2^(to_l s1' - 1))
  (n6_expr:(to_n s6') = (ai O s1')/2 + 2^(to_l s1' - 2))

  (a60_expr:ai 1 s1' + 2 ^ (to_l s1' - 2) + divpow2r (to_n s5') 0 + 1 =
  fst s6' + divpow2r (to_n s4') 0 + divpow2r (to_n s3') 1)

  (a6_expr:forall i : nat,
    ai (S (S i)) s1' + (if S (S i) =? to_l s1' - 1 then 1 else 0) + divpow2r (2^(to_l s1') - 1) (S (S i)) +
    divpow2r (to_n s5') (S i) = ai i s6' + divpow2r (to_n s4') (S i) + divpow2r (to_n s3') (S (S i))):

  weakly_embanked s1' s6' (to_n s3') (to_n s4') (to_n s5') (to_n s6').



Inductive embanked: (nat*(list nat))->(nat*(list nat))->nat->nat->nat->nat->Prop :=
| embanked_intro n1' s1' s6' s7' s8' s_1' h_1' s_2' h_2'
  (Hwemb:weakly_embanked s1' s6' s_1' h_1' s_2' h_2')
  (I67:Increments n1' s6' s7')
  (Z78:Zero s7' s8')

  (H_a60_ge_n6:fst s6' >= h_2')

  (a70_expr : ai 1 s1' + 2 ^ (to_l s1' - 2) + divpow2r s_2' 0 - (to_n s7') + 1 =
           fst s7' + h_2' + divpow2r h_1' 0 + divpow2r s_1' 1)
  (a7_expr : forall i : nat,
          ai (S (S i)) s1' + (if S (S i) =? (to_l s1') - 1 then 1 else 0) +
          divpow2r (2 ^ (to_l s1') - 1) (S (S i)) + divpow2r s_2' (S i) + divpow2r h_2' i =
          ai i s7' + divpow2r h_1' (S i) + divpow2r s_1' (S (S i)))

  (Hwf7:WF1 s7')
  (Hs7s:to_s s7' = false)
  (Hs7n:to_n s7' = O)
  (Hl_eq:to_l s1' = to_l s7'):
  embanked s1' s7' s_1' h_1' s_2' h_2'.


Definition ai' i s :=
  match i with
  | O => fst s
  | S i0 => ai i0 s
  end.

Inductive Add2: nat->(nat*(list nat))->(nat*(list nat))->Prop :=
| Add2_intro i0 s1 s2
  (Hadd2:forall i, ai' i s1 + (if Nat.eqb i i0 then 2 else 0) = ai' i s2):
  Add2 i0 s1 s2
.



Lemma Zero_a0 {s1 s2}:
  Zero s1 s2 ->
  fst s1 = S (fst s2).
Proof.
  intro Z.
  inverts Z.
  reflexivity.
Qed.

Lemma Zero_a1 {s1 s2}:
  Zero s1 s2 ->
  to_l s1 >= 3 ->
  ai O s1 = ai O s2.
Proof.
  intros Z Hl.
  inverts Z.
  cbn in Hl.
  cbn.
  destruct xs.
  1: cbn in Hl; lia.
  reflexivity.
Qed.

Lemma Zero_a {s1 s2}:
  Zero s1 s2 ->
  forall i, ai i s1 + (if Nat.eqb i (to_l s1 - 1) then 1 else 0)%nat = ai i s2.
Proof.
  unfold ai.
  intros Z i.
  inverts Z.
  cbn.
  rewrite grey_to_binary_length,length_map,length_app.
  cbn.
  replace (length xs + 1 - 1) with (length xs) by lia.
  destruct (Nat.eqb_spec i (length xs)) as [E|E].
  - subst i. do 2 rewrite nth_middle.
    lia.
  - assert (i<length xs\/i>length xs) as [E0|E0] by lia.
    + do 2 (rewrite app_nth1; auto 1).
    + do 2 (rewrite app_nth2; try lia).
      destruct (i-length xs) as [|v1] eqn:E1. 1: lia.
      cbn.
      destruct v1 as [|[|[|]]]; reflexivity.
Qed.

Lemma Overflow_a0 {s1 s2}:
  Overflow s1 s2 ->
  fst s1 = fst s2.
Proof.
  intro Ov.
  inverts Ov.
  reflexivity.
Qed.

Lemma Overflow_a {s1 s2}:
  Overflow s1 s2 ->
  forall i, ai i s1 + (if Nat.eqb i (to_l s1 - 1) then 1 else 0)%nat = ai i s2.
Proof.
  intro Ov.
  inverts Ov.
  unfold ai.
  cbn.
  rewrite grey_to_binary_length,length_map,length_app.
  cbn.
  rewrite add_sub.
  intro i.
  destruct (Nat.eqb_spec i (length xs)) as [E|E].
  - subst i. do 2 rewrite nth_middle.
    lia.
  - assert (i<length xs\/i>length xs) as [E0|E0] by lia.
    + do 2 (rewrite app_nth1; auto 1).
    + do 2 (rewrite app_nth2; try lia).
      destruct (i-length xs) as [|v1] eqn:E1. 1: lia.
      cbn.
      destruct v1 as [|[|[|]]]; reflexivity.
Qed.

Lemma Halve_a0 {s1 s2}:
  Halve s1 s2 ->
  fst s2 = S (ai O s1).
Proof.
  intro H.
  inverts H.
  reflexivity.
Qed.

Lemma Halve_a {s1 s2}:
  Halve s1 s2 ->
  forall i, ai i s2 = ai (S i) s1.
Proof.
  intro H.
  inverts H.
  reflexivity.
Qed.

Lemma Increments_sgn {n s1 s2}:
  Increments n s1 s2 ->
  to_s s1 = to_s s2.
Proof.
  intro H.
  induction H.
  1: reflexivity.
  pose proof (Increment_sgn H).
  congruence.
Qed.

Lemma Increments_n {n s1 s2}:
  Increments n s1 s2 ->
  if to_s s1 then
    to_n s1 + n = to_n s2
  else
    to_n s1 = to_n s2 + n.
Proof.
  intro H.
  induction H.
  1: destruct (to_s s); lia.
  pose proof (Increment_n H) as Hn.
  pose proof (Increment_sgn H) as Hs.
  rewrite <-Hs in IHIncrements.
  destruct (to_s s2); lia.
Qed.

Lemma Increments_len {n s1 s2}:
  Increments n s1 s2 ->
  to_l s1 = to_l s2.
Proof.
  intro H.
  induction H.
  1: reflexivity.
  pose proof (Increment_len H).
  congruence.
Qed.

Lemma div2ceil_pow2sub1 n:
  n<>O ->
  (2^n - 1 + 1)/2 = 2^(n-1).
Proof.
  intro H.
  destruct n. 1: congruence.
  rewrite pow2_1a.
  pose proof (pow2_nez n).
  replace (S n - 1) with n by lia.
  replace (2*2^n-1+1) with (2^n*2) by lia.
  rewrite div_mul; lia.
Qed.

Lemma divpow2r_0 n:
  divpow2r n O = (n+1)/2.
Proof.
  reflexivity.
Qed.

Lemma div2ceil_div2floor_Odd n:
  Odd n ->
  (n+1)/2 = n/2 + 1.
Proof.
  intro H.
  inverts H.
  rewrite (mul_comm 2 x).
  rewrite <-add_assoc.
  cbn[add].
  rewrite div_add_l. 2: lia.
  rewrite div_add_l. 2: lia.
  cbn; lia.
Qed.

Lemma div2ceil_div2floor_Even n:
  Even n ->
  (n+1)/2 = n/2.
Proof.
  intro H.
  inverts H.
  rewrite mul_comm,div_add_l. 2: lia.
  rewrite div_mul. 2: lia.
  cbn; lia.
Qed.

Lemma div2ceil_div2floor n:
  (n+1)/2 = n/2 + 1 \/
  (n+1)/2 = n/2.
Proof.
  destruct (Even_or_Odd n).
  - right.
    apply div2ceil_div2floor_Even,H.
  - left.
    apply div2ceil_div2floor_Odd,H.
Qed.

Lemma div2_add_Odd n1 n2:
  Odd n1 ->
  Odd n2 ->
  n1/2 + n2/2 + 1 = (n1+n2)/2.
Proof.
  intros.
  inverts H.
  inverts H0.
  repeat rewrite (mul_comm 2).
  rewrite div_add_l. 2: congruence.
  rewrite div_add_l. 2: congruence.
  replace (x*2+1+(x0*2+1)) with ((x+x0+1)*2) by lia.
  rewrite div_mul. 2: congruence.
  cbn; lia.
Qed.


Lemma pow2_div2 i:
  i<>O ->
  2^i/2 = 2^(i-1).
Proof.
  destruct i as [|i].
  1: congruence.
  intro.
  replace (2^S i) with (2^(S i - 1 + 1)) by (f_equal; lia).
  rewrite pow_add_r.
  change (2^1) with 2.
  rewrite div_mul; congruence.
Qed.

Lemma pow2_add i:
  2^i + 2^i = 2^(i+1).
Proof.
  rewrite (add_comm i),pow2_1a.
  lia.
Qed.

Lemma pow2_sub1 a i:
  a+1 = 2^i <->
  a = 2^i - 1.
Proof.
  pose proof (pow2_nez i).
  lia.
Qed.

Lemma pow2_Even i:
  i<>O ->
  Even (2^i).
Proof.
  destruct i as [|i].
  1: congruence.
  intro.
  rewrite pow2_1a.
  econstructor.
  reflexivity.
Qed.

Lemma div2_add2 a:
  (a+2)/2 = a/2+1.
Proof.
  replace (a+2) with (1*2+a) by lia.
  rewrite div_add_l. 2: congruence.
  lia.
Qed.


(*
  Proposition 3.4
  and also prove some properties of s_1,s_2,h_1,h_2 for Lemma 3.5
*)
Lemma weakly_embanked_precond s1:
  WF1 s1 ->
  to_s s1 = false ->
  to_n s1 = O ->
  to_l s1 >= 3 ->
  Odd (fst s1) ->
  fst s1 < 2 ^ to_l s1 - 1 ->
  ai O s1 < 3 * (2 ^ (to_l s1 - 1)) ->
  exists s2 s_1 s_2 h_1 h_2,
  weakly_embanked s1 s2 s_1 h_1 s_2 h_2.
Proof.
  intros Hwf1 Hs1s Hs1n Hs1l Hs1a0_odd Hs1a0_lt Hs1a1_lt.
  destruct (Zero_precond Hwf1 Hs1s Hs1n) as [s2 [Z12 Hwf2]].
  pose proof (Zero_sgn Z12) as Hs2s.
  pose proof (Zero_n Z12) as Hs2n.
  pose proof (Zero_len Z12) as Hs2l.
  pose proof (Zero_a0 Z12) as Hs2a0.
  pose proof (Zero_a1 Z12 Hs1l) as Hs2a1.
  pose proof (Zero_a Z12) as Hs2a.
  assert (Hs2a0_even:Even (fst s2)). {
    rewrite Hs2a0 in Hs1a0_odd.
    rewrite Odd_succ in Hs1a0_odd.
    apply Hs1a0_odd.
  }
  assert (Hs2n_odd:Odd (to_n s2)). {
    rewrite Hs2n.
    replace (to_l s1) with (1+(to_l s1 - 1)) by lia.
    rewrite pow2_1a.
    pose proof (pow2_nez (to_l s1 - 1)).
    destruct (2 ^ (to_l s1 - 1)). 1: congruence.
    replace (2*(S n)-1) with (S (2*n)) by lia.
    rewrite Odd_succ.
    econstructor; reflexivity.
  }
  eassert (I23:_). {
    apply (Increments_dec_precond2 (fst s2) Hwf2 Hs2s).
    2: lia.
    rewrite <-Hs2a0.
    rewrite Hs2n.
    lia.
  }
  destruct I23 as [s3 [I23 Hwf3]].
  pose proof (Increments_sgn I23) as Hs3s.
  pose proof (Increments_n I23) as Hs3n.
  pose proof (Increments_len I23) as Hs3l.
  pose proof (Increments_a0 I23) as Hs3a0.
  pose proof (Increments_a I23) as Hs3a.
  rewrite Hs2s in Hs3n,Hs3a0,Hs3a.
  pose proof (Hs3a O) as Hs3a1.
  assert (Hs3a0_0:fst s3 = O) by lia.
  clear Hs3a0.
  assert (Hs3n_odd:Odd (to_n s3)). {
    rewrite Hs3n in Hs2n_odd.
    apply (Odd_add_Odd_inv_l _ _ Hs2n_odd Hs2a0_even).
  }
  pose proof (div2ceil_div2floor_Odd _ Hs3n_odd) as Hs3n_div2.
  assert (Hs3ngt1:to_n s3 > 1%nat) by lia.

  edestruct (Halve_precond2 Hwf3 Hs3a0_0) as [s4 [H34 Hwf4]]. 1: lia.
  pose proof (Halve_sgn H34) as Hs4s.
  pose proof (Halve_n H34) as Hs4n.
  pose proof (Halve_len H34) as Hs4l.
  pose proof (Halve_a0 H34) as Hs4a0.
  pose proof (Halve_a H34) as Hs4a.
  rewrite <-Hs3s,Hs2s in Hs4s.
  cbn in Hs4s; symmetry in Hs4s.

  rewrite Hs2n in Hs3a1.
  do 2 rewrite divpow2r_0 in Hs3a1.
  rewrite div2ceil_pow2sub1 in Hs3a1. 2: lia.
  rewrite div2_div in Hs4n.
  rewrite Hs3n_div2 in Hs3a1.

  remember (ai O s1) as a11.
  remember (ai O s2) as a21.
  remember (ai O s3) as a31.
  remember (ai O s4) as a41.
  remember (fst s1) as a10.
  remember (fst s2) as a20.
  remember (fst s3) as a30.
  remember (fst s4) as a40.
  remember (to_n s1) as n1.
  remember (to_n s2) as n2.
  remember (to_n s3) as n3.
  remember (to_n s4) as n4.
  remember (to_l s1) as l1.
  remember (to_l s2) as l2.
  remember (to_l s3) as l3.
  remember (to_l s4) as l4.
  assert (H_a11_a40:a11 + 2 ^ (l1 - 1) = a40 + n3 / 2) by lia.
  assert (Hn3_expr:n3 + a10 = 2^l1) by lia.
  assert (Hn4_expr:n4 + a10/2 + 1 = 2^(l1-1)). {
    rewrite <-Hs4n.
    replace (l1) with (1+(l1-1)) in Hn3_expr by lia.
    rewrite pow2_1a,mul_comm in Hn3_expr.
    replace (2^(l1-1)) with (2^(l1-1)*2/2) by (apply div_mul; congruence).
    rewrite div2_add_Odd; auto 1.
    congruence.
  }
  eassert (I45:_). {
    apply (Increments_inc_precond2 (fst s4) Hwf4 Hs4s).
    3: lia.
    - rewrite <-Heqn4,<-Heqa40,<-Heql4.
      rewrite <-Hs4n.
      replace (l4-2) with (l1-1) by lia.
      lia.
    - rewrite <-Heqn4,<-Heqa40,<-Heql4.
      rewrite <-Hs4n.
      replace (l4) with (l1+1) by lia.
      replace (l1+1) with (1+(1+(l1-1))) by lia.
      do 2 rewrite pow2_1a.
      lia.
  }
  rewrite <-Heqa40 in I45.
  destruct I45 as [s5 [I45 Hwf5]].
  pose proof (Increments_sgn I45) as Hs5s.
  pose proof (Increments_n I45) as Hs5n.
  pose proof (Increments_len I45) as Hs5l.
  pose proof (Increments_a0 I45) as Hs5a0.
  pose proof (Increments_a I45) as Hs5a.
  rewrite Hs4s in Hs5n,Hs5a0,Hs5a.
  assert (Hs5a0_0:fst s5 = O) by lia.
  clear Hs5a0.

  remember (to_n s5) as n5.
  rewrite <-Heqn4 in Hs5n.

  assert (Hn5_expr:n5 = a11 + 2^(l1-1)) by lia.

  edestruct (Halve_precond1 Hwf5 Hs5a0_0) as [s6 [H56 Hwf6]]. 1: lia.
  pose proof (Halve_sgn H56) as Hs6s.
  pose proof (Halve_n H56) as Hs6n.
  pose proof (Halve_len H56) as Hs6l.
  pose proof (Halve_a0 H56) as Hs6a0.
  pose proof (Halve_a H56) as Hs6a.
  rewrite <-Hs5s,Hs4s in Hs6s.
  cbn in Hs6s. symmetry in Hs6s.

  remember (to_n s6) as n6.
  rewrite <-Heqn5 in Hs6n.
  rewrite div2_div in Hs6n.
  assert (Hn6_expr:n6 = a11/2 + 2^(l1-2)). {
    replace (l1-1) with (1+(l1-2)) in Hn5_expr by lia.
    rewrite pow2_1a in Hn5_expr.
    rewrite <-Hs6n,Hn5_expr,mul_comm,add_comm.
    rewrite div_add_l. 2: congruence.
    apply add_comm.
  }

  remember (fst s6) as a60.

  assert (Hs5a_expr:forall i,
  ai (S i) s1 + (if S i =? l1 - 1 then 1 else 0) + divpow2r n2 (S i) + divpow2r n5 i =
  ai i s5 + divpow2r n4 i + divpow2r n3 (S i)). {
    intro i.
    specialize (Hs2a (S i)).
    specialize (Hs3a (S i)).
    specialize (Hs4a i).
    specialize (Hs5a i).
    subst.
    lia.
  }
  assert (Ha60_expr:
  ai 1 s1 + (2^(l1-2)) + divpow2r n5 0 + 1 =
  a60 + divpow2r n4 0 + divpow2r n3 1). {
    specialize (Hs5a_expr O).
    destruct (Nat.eqb_spec 1 (l1-1)).
    1: lia.
    rewrite add_0_r in Hs5a_expr.
    rewrite Hs6a0.
    replace (2^(l1-2)) with (divpow2r n2 1). 2:{
      unfold divpow2r.
      rewrite Hs2n.
      change (2^1) with 2.
      change (2^(1+1)) with (2*2).
      rewrite <-Div0.div_div.
      replace ((2^l1)-1+2) with (2^l1+1) by (pose proof (pow2_nez l1); lia).
      rewrite div2ceil_div2floor_Even. 2: apply pow2_Even; lia.
      do 2 (rewrite pow2_div2; [idtac|lia]).
      f_equal. lia.
    }
    lia.
  }
  assert (Hs6a_expr:forall i,
  ai (S (S i)) s1 + (if S (S i) =? l1 - 1 then 1 else 0) + divpow2r (2^l1-1) (S (S i)) + divpow2r n5 (S i) =
  ai i s6 + divpow2r n4 (S i) + divpow2r n3 (S (S i))). {
    intro i.
    specialize (Hs2a (S (S i))).
    specialize (Hs3a (S (S i))).
    specialize (Hs4a (S i)).
    specialize (Hs5a (S i)).
    specialize (Hs6a i).
    rewrite <-Hs2n.
    subst.
    lia.
  }
  subst.
  do 5 eexists.
  econstructor.
  - apply Z12.
  - apply I23.
  - apply H34.
  - rewrite Hs4a0 in I45.
    apply I45.
  - apply H56.
  - apply Hwf1.
  - apply Hs1s.
  - apply Hs1n.
  - apply Hs1l.
  - apply Hs1a0_odd.
  - apply Hs1a0_lt.
  - apply Hs1a1_lt.
  - apply Hwf6.
  - apply Hs6s.
  - lia.
  - constructor. congruence.
  - constructor. congruence.
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - apply Ha60_expr.
  - apply Hs6a_expr.
Qed.

Lemma embanked_precond {s1 s6 s_1 h_1 s_2 h_2}:
  weakly_embanked s1 s6 s_1 h_1 s_2 h_2 ->
  h_2 <= fst s6 ->
  exists s7, embanked s1 s7 s_1 h_1 s_2 h_2.
Proof.
  intros Hweb Hn6_le.
  inversion Hweb; subst.
  assert (H_a60_ge_n6:fst s6 >= to_n s6) by lia.
  eassert (I67:_). {
    apply (Increments_dec_precond1 (to_n s6) Hwf6' Hs6s); auto 1; lia.
  }
  destruct I67 as [s7 [I67 Hwf7]].
  pose proof (Increments_sgn I67) as Hs7s.
  pose proof (Increments_n I67) as Hs7n.
  pose proof (Increments_len I67) as Hs7l.
  pose proof (Increments_a0 I67) as Hs7a0.
  pose proof (Increments_a I67) as Hs7a.
  rewrite Hs6s in Hs7n,Hs7a0,Hs7a.

  eassert (Z78:_). {
    apply (Zero_precond Hwf7).
    - congruence.
    - lia.
  }
  destruct Z78 as [s8 [Z78 Hwf8]].

  remember (to_l s1) as l1.
  remember (to_l s6) as l6.
  remember (to_l s7) as l7.
  remember (to_n s3') as n3.
  remember (to_n s4') as n4.
  remember (to_n s5') as n5.
  remember (to_n s6) as n6.
  remember (to_n s7) as n7.

  assert(a70_expr : ai 1 s1 + 2 ^ (l1 - 2) + divpow2r n5 0 - n7 + 1 =
           fst s7 + n6 + divpow2r n4 0 + divpow2r n3 1) by lia.
  assert(a7_expr : forall i : nat,
          ai (S (S i)) s1 + (if S (S i) =? l1 - 1 then 1 else 0) +
          divpow2r (2 ^ l1 - 1) (S (S i)) + divpow2r n5 (S i) + divpow2r n6 i =
          ai i s7 + divpow2r n4 (S i) + divpow2r n3 (S (S i))). {
    intro i.
    assert (divpow2r n7 i = O). {
      assert (Hn7_0:n7=O) by lia.
      rewrite Hn7_0.
      unfold divpow2r. cbn.
      rewrite add_comm,div_small.
      1: reflexivity.
      cbn. pose proof (pow2_nez i); lia.
    }
    specialize (a6_expr i).
    specialize (Hs7a i).
    lia.
  }

  subst.
  exists s7.
  econstructor.
  - apply Hweb.
  - apply I67.
  - apply Z78.
  - apply H_a60_ge_n6.
  - apply a70_expr.
  - apply a7_expr.
  - apply Hwf7.
  - congruence.
  - lia.
  - lia.
Qed.




(* Lemma 3.5 *)
Lemma emb_wemb_s_h {e ne nne i s_1 h_1 s_2 h_2 s_1' h_1' s_2' h_2'}:
  embanked e ne s_1 h_1 s_2 h_2 ->
  weakly_embanked ne nne s_1' h_1' s_2' h_2' ->
  Add2 i e ne ->
  match i with
  | O => (s_1,h_1,s_2,h_2) = (s_1'+2,h_1'+1,s_2',h_2')
  | S O => (s_1,h_1,s_2+2,h_2+1) = (s_1',h_1',s_2',h_2')
  | _ => (s_1,h_1,s_2,h_2) = (s_1',h_1',s_2',h_2')
  end.
Proof.
  intros He Hwe Hadd.
  inversion He. subst.
  inversion Hwemb. subst.
  inversion Hwe. subst.
  inversion Hadd. subst.
  pose proof (Hadd2 O) as Hadd2_0.
  pose proof (Hadd2 (S O)) as Hadd2_1.
  cbn in Hadd2_0,Hadd2_1.
  remember (to_n s3') as s_1.
  remember (to_n s4') as h_1.
  remember (to_n s5') as s_2.
  remember (to_n s6') as h_2.
  remember (to_n s3'0) as s_1'.
  remember (to_n s4'0) as h_1'.
  remember (to_n s5'0) as s_2'.
  remember (to_n nne) as h_2'.
  remember (to_l e) as l1.
  remember (to_l ne) as l1'.
  remember (fst e) as a10.
  remember (fst ne) as a10'.
  remember (ai 0 e) as a11.
  remember (ai 0 ne) as a11'.
  rewrite <-Hl_eq in Heql1'.
  subst l1'.
  rewrite <-Hadd2_0 in Heqa10'.
  subst a10'.
  rewrite <-Hadd2_1 in Heqa11'.
  subst a11'.
  destruct i as [|[|i]].
  - rewrite div2_add2 in n4_expr0.
    rewrite add_0_r in n6_expr0.
    repeat f_equal; lia.
  - rewrite add_0_r in n4_expr0.
    rewrite div2_add2 in n6_expr0.
    repeat f_equal; lia.
  - rewrite add_0_r in n4_expr0.
    rewrite add_0_r in n6_expr0.
    repeat f_equal; lia.
Qed.

Lemma Nat_eqb_def a b:
  Nat.eqb (S a) (S b) = Nat.eqb a b.
Proof.
  reflexivity.
Qed.

Lemma divpow2r_mono n1 n2 i:
  n1 <= n2 ->
  divpow2r n1 i <=
  divpow2r n2 i.
Proof.
  intro H.
  unfold divpow2r.
  apply Div0.div_le_mono.
  lia.
Qed.


Lemma divpow2r_div2 n i:
  divpow2r (n/2) i = divpow2r n (S i).
Proof.
  unfold divpow2r.
  cbn[add].
  do 2 rewrite pow2_1a.
  rewrite <-Div0.div_div.
  replace (n+2*2^i) with (2*(n/2)+(n mod 2)+2*2^i). 2:{
    f_equal.
    rewrite <-div_mod; congruence.
  }
  replace (2*(n/2) + n mod 2 + 2 * 2 ^ i) with
  ((n/2+2^i)*2 + n mod 2) by lia.
  rewrite div_add_l. 2: congruence.
  rewrite (div_small (n mod 2)).
  2: apply mod_upper_bound; congruence.
  f_equal.
  lia.
Qed.

Lemma divpow2r_div2_add2 n i:
  divpow2r (n/2+1) i = divpow2r (n+2) (S i).
Proof.
  applys_eq divpow2r_div2.
  f_equal.
  rewrite div2_add2.
  reflexivity.
Qed.

Lemma divpow2r_S n i:
  divpow2r (n+1) i = (divpow2r n i) + (if Nat.eqb (n mod 2^(i+1)) (2^i-1) then 1 else 0).
Proof.
  destruct (Nat.eqb_spec (n mod 2 ^ (i + 1)) (2 ^ i - 1)) as [E|E].
  - symmetry. apply divpow2r_inc,E.
  - symmetry. rewrite divpow2r_eq. 2: apply E.
    apply add_0_r.
Qed.

Require Import ZArith.
Fixpoint ctz(x:positive):nat :=
match x with
| xO x0 => S (ctz x0)
| _ => O
end.

Definition ctzS(n:nat):nat :=
  ctz (Pos.of_succ_nat n).

Lemma ctzS_spec_0 n0:
  forall n i,
  n<n0 ->
  ctzS n = i <->
  n mod 2^(i+1) = 2^i-1.
Proof.
  induction n0.
  1: lia.
  intros.
  assert (n<n0\/n=n0) as E by lia.
  destruct E as [E|E].
  1: apply IHn0; auto 1.
  subst n. clear H.
  unfold ctzS.
  destruct (Pos.of_succ_nat n0) eqn:E; cbn.
  - assert (H:n0 = (Pos.to_nat p)*2) by lia.
   destruct i as [|i].
    + change (2^(0+1)) with 2.
      change (2^0-1)%nat with 0%nat.
      rewrite H,Div0.mod_mul.
      tauto.
    + cbn[add].
      rewrite pow2_1a,H.
      rewrite mul_comm,Div0.mul_mod_distr_l.
      rewrite pow2_1a.
      pose proof (pow2_nez i).
      lia.
  - destruct i as [|i].
    + split. 1: lia.
      change (2^(0+1)) with 2.
      change (2^0-1)%nat with 0%nat.
      assert (H:n0 = (Pos.to_nat p - 1)*2+1) by lia.
      rewrite H.
      rewrite Div0.add_mul_mod_distr_r with (b:=1%nat); lia.
    + rewrite succ_inj_wd.
      assert (H:n0 = (Pos.to_nat p - 1)*2+1) by lia.
      assert (H0:n0/2 = Pos.to_nat p - 1). {
        rewrite H.
        rewrite div_add_l. 2: congruence.
        cbn. lia.
      }
      assert (H1:n0/2<n0) by lia.
      specialize (IHn0 _ i H1).
      unfold ctzS in IHn0.
      rewrite H0 in IHn0.
      replace (Pos.of_succ_nat (Pos.to_nat p - 1)) with p in IHn0 by lia.
      rewrite <-H0 in IHn0,H.
      rewrite IHn0.
      remember (n0/2) as n1.
      rewrite H.
      cbn[add].
      do 2 rewrite pow2_1a.
      rewrite mul_comm.
      rewrite Div0.add_mul_mod_distr_l. 2: lia.
      pose proof (pow2_nez i).
      lia.
  - assert (n0 = O) by lia.
    subst.
    rewrite Div0.mod_0_l.
    destruct i as [|i].
    + cbn. tauto.
    + pose proof (pow2_nez i).
      rewrite pow2_1a.
      lia.
Qed.


Lemma ctzS_spec n i:
  ctzS n = i <->
  n mod 2^(i+1) = 2^i-1.
Proof.
  apply (ctzS_spec_0) with (n0:=S n).
  lia.
Qed.

Ltac gsubst a a_eq :=
  remember a as tmp eqn:Heqtmp;
  rewrite <-a_eq in Heqtmp;
  subst tmp; clear Heqtmp.

Ltac gsubst_l a a_eq :=
  remember a as tmp eqn:Heqtmp;
  rewrite a_eq in Heqtmp;
  subst tmp; clear Heqtmp.

Ltac lia_gsubst a b:=
  assert (b=a) as Htmp by lia;
  gsubst a Htmp.


(* Proposition 3.6 *)
Lemma emb_wemb_Add2_emb {e ne ne' i s_1 h_1 s_2 h_2 s_1' h_1' s_2' h_2'}:
  embanked e ne s_1 h_1 s_2 h_2 ->
  weakly_embanked ne ne' s_1' h_1' s_2' h_2' ->
  Add2 i e ne ->
  exists nne, embanked ne nne s_1' h_1' s_2' h_2' /\
  match i with
  | O => Add2 (ctzS (h_1-1)) ne nne
  | S O => Add2 (S (ctzS h_2)) ne nne
  | S (S i0) => Add2 i0 ne nne
  end.
Proof.
  intros He Hwe Hadd.
  pose proof (emb_wemb_s_h He Hwe Hadd) as H_s_h.
  inversion He. subst.
  inversion Hwemb. subst.
  inversion Hwe. subst.
  inversion Hadd. subst.
  pose proof (Hadd2 O) as Hadd2_0.
  pose proof (Hadd2 (S O)) as Hadd2_1.
  cbn in Hadd2_0,Hadd2_1.
  remember (to_n s3') as s_1.
  remember (to_n s4') as h_1.
  remember (to_n s5') as s_2.
  remember (to_n s6') as h_2.
  remember (to_n s3'0) as s_1'.
  remember (to_n s4'0) as h_1'.
  remember (to_n s5'0) as s_2'.
  remember (to_n ne') as h_2'.
  remember (to_l e) as l1.
  remember (to_l ne) as l1'.
  remember (fst e) as a10.
  remember (fst ne) as a10'.
  remember (ai 0 e) as a11.
  remember (ai 0 ne) as a11'.
  rewrite <-Hl_eq in Heql1'.
  subst l1'.
  rewrite <-Hadd2_0 in Heqa10'.
  subst a10'.
  rewrite <-Hadd2_1 in Heqa11'.
  subst a11'.
  destruct i as [|[|i]].
  {
    inversion H_s_h.
    rewrite H0 in Heqs_1,n3_expr.
    rewrite H1 in Heqh_1,n4_expr.
    rewrite H2 in Heqs_2,n5_expr.
    rewrite H3 in Heqh_2,n6_expr.
    subst s_1 h_1 s_2 h_2.
    rewrite div2_add2 in n4_expr0.
    rewrite add_0_r in n6_expr0.

    epose proof (divpow2r_mono h_1' (h_1'+1) 0 _) as E1.
    Unshelve. 2: lia.
    epose proof (divpow2r_mono s_1' (s_1'+2) 1 _) as E2.
    Unshelve. 2: lia.
    pose proof (Hadd2 2) as Hadd2_2.
    cbn in Hadd2_2.

    epose proof (embanked_precond Hwe _) as He'.
    Unshelve. 2: lia.
    destruct He' as [nne He'].
    exists nne.
    split. 1: apply He'.
    inversion He'. subst s1' s7' s_1'0 h_1'0 s_2'0 h_2'0.
    rewrite <-Heql1' in a70_expr0,a7_expr0.

    assert (Ha:
    forall i:nat,
      ai' i ne + 2*(divpow2r (h_1' + 1) i) =
      ai' i nne + 2*(divpow2r h_1' i)
    ). {
      destruct n34_expr0 as [n34_expr0].
      destruct n56_expr0 as [n56_expr0].
      assert (H1:forall i,divpow2r (s_1' + 2) (S i) = (divpow2r (h_1' + 1) i)). {
        intro i.
        rewrite <-divpow2r_div2_add2.
        congruence.
      }
      assert (H2:forall i,divpow2r (s_1') (S i) = (divpow2r (h_1') i)). {
        intro i.
        rewrite <-divpow2r_div2.
        congruence.
      }
      intro i0.
      destruct i0 as [|i0].
      - specialize (H1 O).
        specialize (H2 O).
        unfold ai'.
        lia.
      - specialize (H1 (S i0)).
        specialize (H2 (S i0)).
        unfold ai'.
        specialize (a7_expr i0).
        specialize (a7_expr0 i0).
        pose proof (Hadd2 (S (S (S i0)))) as Hadd2_S.
        cbn in Hadd2_S.
        lia.
    }
    constructor.
    intro i.
    specialize (Ha i).
    rewrite add_sub.
    destruct (Nat.eqb_spec i (ctzS h_1')) as [E|E].
    - symmetry in E.
      rewrite ctzS_spec in E.
      rewrite <-divpow2r_inc in Ha. 2: apply E. lia.
    - pose proof (not_eq_sym E) as E'.
      rewrite ctzS_spec in E'.
      rewrite <-divpow2r_eq in Ha. 2: apply E'. lia.
  }
  {
    inversion H_s_h.
    rewrite <-H0 in Heqs_1',n3_expr0.
    rewrite <-H1 in Heqh_1',n4_expr0.
    rewrite <-H2 in Heqs_2',n5_expr0.
    rewrite <-H3 in Heqh_2',n6_expr0.
    subst s_1' h_1' s_2' h_2'.
    rewrite add_0_r in n4_expr0.
    rewrite div2_add2 in n6_expr0.

    pose proof (Hadd2 2) as Hadd2_2.
    cbn in Hadd2_2.
    assert ((divpow2r s_2 0) + 1 = divpow2r (s_2+2) 0). {
      repeat rewrite divpow2r_0.
      replace (s_2+2+1) with (s_2+1+2) by lia.
      rewrite div2_add2.
      reflexivity.
    }
    epose proof (embanked_precond Hwe _) as He'.
    Unshelve. 2: lia.
    destruct He' as [nne He'].
    exists nne.
    split. 1: apply He'.
    inversion He'. subst s1' s7' s_1' h_1' s_2' h_2'.
    rewrite <-Heql1' in a70_expr0,a7_expr0.

    assert (Ha:
    forall i,
      ai i ne + 2*(divpow2r (h_2 + 1) i) =
      ai i nne + 2*(divpow2r h_2 i)
    ). {
      intro i0.
      pose proof (Hadd2 (S (S (S i0)))) as Hadd2_S.
      cbn in Hadd2_S.
      destruct n34_expr as [n34_expr].
      destruct n56_expr as [n56_expr].
      assert (divpow2r (s_2 + 2) (S i0) = (divpow2r (h_2 + 1) i0)). {
        rewrite <-divpow2r_div2_add2.
        congruence.
      }
      assert (divpow2r (s_2) (S i0) = (divpow2r (h_2) i0)). {
        rewrite <-divpow2r_div2.
        congruence.
      }
      specialize (a7_expr i0).
      specialize (a7_expr0 i0).
      lia.
    }

    assert (Ha0:
      (fst ne) + divpow2r (s_2 + 2) 0 =
      (fst nne) + divpow2r s_2 0 + 1
    ) by lia.

    constructor.
    intro i.
    destruct i as [|i].
    - unfold ai'.
      do 2 rewrite divpow2r_0 in Ha0.
      replace (s_2+2+1) with (s_2+1+2) in Ha0 by lia.
      rewrite div2_add2,<-add_assoc,add_cancel_r in Ha0.
      cbn. lia.
    - unfold ai'.
      rewrite Nat_eqb_def.
      specialize (Ha i).
      destruct (Nat.eqb_spec i (ctzS h_2)) as [E|E].
      + symmetry in E.
        rewrite ctzS_spec in E.
        rewrite <-divpow2r_inc in Ha. 2: apply E. lia.
      + pose proof (not_eq_sym E) as E'.
        rewrite ctzS_spec in E'.
        rewrite <-divpow2r_eq in Ha. 2: apply E'. lia.
  }
  {
    inversion H_s_h.
    rewrite <-H0 in Heqs_1',n3_expr0.
    rewrite <-H1 in Heqh_1',n4_expr0.
    rewrite <-H2 in Heqs_2',n5_expr0.
    rewrite <-H3 in Heqh_2',n6_expr0.
    subst s_1' h_1' s_2' h_2'.
    pose proof (Hadd2 2) as Hadd2_2.
    unfold ai' in Hadd2_2.
    repeat rewrite Nat_eqb_def in Hadd2_2.
    assert (H_a60_ge_n6':fst ne' >= h_2) by lia.
    destruct (embanked_precond Hwe H_a60_ge_n6') as [nne He'].
    exists nne.
    split. 1: apply He'.
    inversion He'. subst s1' s7' s_1' h_1' s_2' h_2'.
    rewrite <-Heql1' in a70_expr0,a7_expr0.
    constructor.
    intro i0.
    destruct i0 as [|i0].
    - unfold ai'.
      lia.
    - unfold ai'.
      specialize (a7_expr i0).
      specialize (a7_expr0 i0).
      specialize (Hadd2 (S (S (S i0)))).
      unfold ai' in Hadd2.
      repeat rewrite Nat_eqb_def in Hadd2.
      lia.
  }
Qed.


Inductive Add2s: nat->(nat*(list nat))->(nat*(list nat))->Prop :=
| Add2s_intro i0 s1 s2
  (Hadd2s:forall i, ai' i s1 + (if andb (i <=? i0) (Bool.eqb (even i) (even i0)) then 2 else 0)%nat = ai' i s2):
  Add2s i0 s1 s2
.

Lemma Add2s_O s1 s2:
  Add2 O s1 s2 ->
  Add2s O s1 s2.
Proof.
  intro H.
  inversion H; subst.
  constructor.
  intro i.
  specialize (Hadd2 i).
  destruct (Nat.eqb_spec i O).
  1: subst; apply Hadd2.
  destruct (Nat.leb_spec i O).
  1: lia.
  apply Hadd2.
Qed.

Lemma Add2s_SO s1 s2:
  Add2 (S O) s1 s2 ->
  Add2s (S O) s1 s2.
Proof.
  intro H.
  inversion H; subst.
  constructor.
  intro i.
  specialize (Hadd2 i).
  destruct (Nat.eqb_spec i (S O)).
  1: subst; apply Hadd2.
  destruct (Nat.leb_spec i (S O)).
  - assert (i=O) by lia. subst.
    apply Hadd2.
  - apply Hadd2.
Qed.


Lemma Add2s_SS i s1 s2 s3:
  Add2 (S (S i)) s1 s2 ->
  Add2s i s2 s3 ->
  Add2s (S (S i)) s1 s3.
Proof.
  intros H H0.
  inversion H; subst.
  inversion H0; subst.
  constructor.
  intro i0.
  specialize (Hadd2 i0).
  specialize (Hadd2s i0).
  rewrite even_succ_succ.

  destruct (Nat.leb_spec i0 (S (S i))) as [E0|E0];
  destruct (Nat.leb_spec i0 i) as [E1|E1];
  destruct (Nat.eqb_spec i0 (S (S i))) as [E2|E2];
  destruct (Bool.eqb_spec (even i0) (even i)) as [E3|E3].
  all: cbn; cbn in Hadd2s; try lia.
  - subst.
    rewrite even_succ_succ in E3.
    congruence.
  - assert (i0 = S i) by lia.
    subst.
    generalize E3.
    simpl_oe_S. unfold odd.
    destruct (even i); cbn; congruence.
Qed.



Inductive embanked_batch: nat->(nat*(list nat))->(nat*(list nat))->nat->nat->Prop :=
| embanked_batch_O e ne s_1' h_1' s_2' h_2'
  (He:embanked e ne s_1' h_1' s_2' h_2')
  (Ha:Add2 0 e ne):
  embanked_batch 0 e ne h_1' h_2'
| embanked_batch_SO e ne s_1' h_1' s_2' h_2'
  (He:embanked e ne s_1' h_1' s_2' h_2')
  (Ha:Add2 1 e ne):
  embanked_batch 1 e ne h_1' h_2'
| embanked_batch_SS i e ne n'e s_1 h_1 s_2 h_2
  (He:embanked e ne s_1 h_1 s_2 h_2)
  (Ha:Add2 (S (S i)) e ne)
  (Heb:embanked_batch i ne n'e h_1 h_2):
  embanked_batch (S (S i)) e n'e h_1 h_2
.



Lemma embanked_Add2SS_embanked {i e ne s_1' h_1' s_2' h_2'}:
  embanked e ne s_1' h_1' s_2' h_2' ->
  Add2 (S (S i)) e ne ->
  exists nne,
  embanked ne nne s_1' h_1' s_2' h_2' /\ Add2 i ne nne.
Proof.
  intros He Ha.
  inversion He; subst.
  inversion Hwemb; subst.
  inversion Ha; subst.
  pose proof (Hadd2 0) as Hadd2_0.
  pose proof (Hadd2 1) as Hadd2_1.
  cbn[Nat.eqb] in Hadd2_0,Hadd2_1.
  unfold ai' in Hadd2_0,Hadd2_1.
  rewrite add_0_r in Hadd2_0,Hadd2_1.
  eassert (Hwe:_) by
    (apply weakly_embanked_precond with (s1:=ne); auto 1; congruence).
  destruct Hwe as [ne' [s_1 [s_2 [h_1 [h_2 Hwe]]]]].

  destruct (emb_wemb_Add2_emb He Hwe Ha) as [nne [He' Ha']].
  exists nne.
  split. 2: apply Ha'.
  inversion Hwe; subst.

  gsubst (to_l ne) Hl_eq.
  gsubst (fst ne) Hadd2_0.
  gsubst (ai O ne) Hadd2_1.

  applys_eq He'; lia.
Qed.

Lemma embanked__embanked_batch {i}:
  forall {e ne s_1' h_1' s_2' h_2'},
  embanked e ne s_1' h_1' s_2' h_2' ->
  Add2 i e ne ->
  exists n'e, embanked_batch i e n'e h_1' h_2'.
Proof.
  destruct (Even_or_Odd i) as [E|E]; inverts E.
  - induction x.
    + introv He Ha.
      exists ne.
      econstructor; eauto 1.
    + introv He Ha.
      lia_gsubst (2*(S x)) (S(S(2*x))).
      destruct (embanked_Add2SS_embanked He Ha) as [nne [He' Ha']].
      destruct (IHx _ _ _ _ _ _ He' Ha') as [n'e Heb].
      eexists.
      econstructor; eauto 1.
  - induction x.
    + introv He Ha.
      exists ne.
      econstructor; eauto 1.
    + introv He Ha.
      lia_gsubst (2*(S x)+1) (S(S(2*x+1))).
      destruct (embanked_Add2SS_embanked He Ha) as [nne [He' Ha']].
      destruct (IHx _ _ _ _ _ _ He' Ha') as [n'e Heb].
      eexists.
      econstructor; eauto 1.
Qed.

Lemma embanked_batch_precond_01 {i e ne ne' h_1 h_2 s_1' h_1' s_2' h_2'}:
  (i=0\/i=1) ->
  embanked_batch i e ne h_1 h_2 ->
  weakly_embanked ne ne' s_1' h_1' s_2' h_2' ->
  exists n'ne, embanked_batch (match i with
  | O => (ctzS (h_1-1))
  | S O => (S (ctzS h_2))
  | S (S _) => 0
  end) ne n'ne h_1' h_2'.
Proof.
  intros Hi He Hwe.
  destruct Hi; subst;
    inversion He;
    subst;
    eassert (H_s_h:_) by (eapply emb_wemb_s_h; eauto 1);
    eassert (He':_) by (eapply emb_wemb_Add2_emb; eauto 1);
    cbn in H_s_h,He';
    destruct He' as [nne [He' Ha']];
    apply (embanked__embanked_batch He' Ha').
Qed.

Lemma mod2_SS a:
  S (S a) mod 2 = a mod 2.
Proof.
  replace (S (S a)) with (a+1*2) by lia.
  apply Div0.mod_add.
Qed.

Lemma embanked_batch_last {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  exists e',
  embanked_batch (i mod 2) e' ne h_1 h_2.
Proof.
  intro Heb.
  induction Heb.
  1,2: cbn; exists e;
    econstructor; eauto 1.
  destruct IHHeb as [e' Heb'].
  exists e'.
  rewrite mod2_SS.
  apply Heb'.
Qed.

Lemma embanked_batch_Add2s {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  Add2s i e ne.
Proof.
  intro Heb.
  induction Heb.
  - apply Add2s_O,Ha.
  - apply Add2s_SO,Ha.
  - eapply Add2s_SS; eauto 1.
Qed.

Lemma embanked_batch_precond {i e ne ne' h_1 h_2 s_1' h_1' s_2' h_2'}:
  embanked_batch i e ne h_1 h_2 ->
  weakly_embanked ne ne' s_1' h_1' s_2' h_2' ->
  exists n'ne, embanked_batch (match i mod 2 with
  | O => (ctzS (h_1-1))
  | S O => (S (ctzS h_2))
  | S (S _) => 0
  end) ne n'ne h_1' h_2'.
Proof.
  intros He Hwe.
  destruct (embanked_batch_last He) as [n'ne He0].
  eapply embanked_batch_precond_01; eauto 1.
  epose proof (mod_upper_bound i 2 _).
  Unshelve. 2: congruence.
  lia.
Qed.

Lemma embanked_batch_postcond {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  WF1 ne /\
  to_s ne = false /\
  to_n ne = 0 /\
  to_l ne >=3 /\
  Odd (fst ne).
Proof.
  intro Heb.
  induction Heb.
  1,2: inversion He; subst;
    repeat split; auto 1;
    [ inversion Hwemb; subst; lia |
    apply dec_to_0__a0_Odd; auto 1 ].
  apply IHHeb.
Qed.

Lemma embanked_batch__wemb {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  ai' 0 ne < 2^(to_l ne) - 1 ->
  ai' 1 ne < 2^(to_l ne - 1)*3 ->
  exists ne0 s_1' s_2' h_1' h_2',
  weakly_embanked ne ne0 s_1' h_1' s_2' h_2'.
Proof.
  intros Heb Ha0 Ha1.
  destruct (embanked_batch_postcond Heb) as [H [H0 [H1 [H2 H3]]]].
  cbn in Ha0,Ha1.
  eapply (weakly_embanked_precond); eauto 1.
  rewrite (mul_comm 3).
  apply Ha1.
Qed.

Lemma embanked_batch_precond'{i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  ai' 0 ne < 2^(to_l ne) - 1 ->
  ai' 1 ne < 2^(to_l ne - 1)*3 ->
  exists n'ne,
  match i mod 2 with
  | O => embanked_batch (ctzS (h_1-1)) ne n'ne (h_1-1) h_2
  | S O => embanked_batch (S (ctzS (h_2))) ne n'ne h_1 (h_2+1)
  | _ => False
  end.
Proof.
  intros Heb Ha0 Ha1.
  destruct (embanked_batch__wemb Heb Ha0 Ha1) as [ne0 [s_1' [h_1' [s_2' [h_2' Hwe]]]]].
  destruct (embanked_batch_last Heb) as [e' Heb'].
  epose proof (mod_upper_bound i 2 _).
  Unshelve. 2: lia.
  destruct (i mod 2) as [|[|]] eqn:E.
  3: lia.
  1,2: inversion Heb'; subst;
    epose proof (emb_wemb_s_h He Hwe Ha) as H2;
    cbn in H2;
    inversion H2; subst;
    epose proof (embanked_batch_precond Heb Hwe) as H3.
  1: rewrite add_sub; rewrite add_sub in H3.
  1,2: rewrite E in H3;
    apply H3.
Qed.



Lemma embanked_batch_len {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  to_l e = to_l ne.
Proof.
  intro H.
  induction H;
    inversion He; congruence.
Qed.

Lemma even_true_mod2 i:
  even i = true <-> i mod 2 = 0.
Proof.
  destruct (Even_or_Odd i) as [E|E].
  - inversion E; subst.
    rewrite even_spec.
    lia_gsubst (2*x) (x*2).
    rewrite Div0.mod_mul. tauto.
  - inversion E; subst.
    rewrite even_spec.
    lia_gsubst (2*x+1) (1+x*2).
    rewrite Div0.mod_add.
    cbn.
    split; intro.
    1: Odd_Even_contra.
    congruence.
Qed.

Lemma even_false_mod2 i:
  even i = false <-> i mod 2 = 1.
Proof.
  epose proof (mod_upper_bound i 2 _).
  Unshelve. 2: congruence.
  assert (i mod 2 = 0 \/ i mod 2 = 1) as E by lia.
  split; intro.
  - destruct E as [E|E]. 2: tauto.
    rewrite <-even_true_mod2 in E.
    congruence.
  - destruct (even i) eqn:E0.
    2: congruence.
    rewrite even_true_mod2 in E0. 
    congruence.
Qed.

Lemma embanked_batch_a0_a1 {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  ai' 0 ne = ai' 0 e + (1-(i mod 2))*2 /\
  ai' 1 ne = ai' 1 e + ((i mod 2))*2.
Proof.
  intro Heb.
  pose proof (embanked_batch_Add2s Heb) as Ha.
  inverts Ha.
  split.
  - pose proof (Hadd2s 0) as Ha0.
    destruct (Nat.leb_spec 0 i). 2: lia.
    destruct (even i) eqn:E.
    + cbn in Ha0.
      rewrite even_true_mod2 in E.
      rewrite E.
      cbn. congruence.
    + cbn in Ha0.
      rewrite even_false_mod2 in E.
      rewrite E.
      cbn. congruence.
  - pose proof (Hadd2s 1) as Ha0.
    destruct (Nat.leb_spec 1 i).
    + destruct (even i) eqn:E.
      * cbn in Ha0.
        rewrite even_true_mod2 in E.
        rewrite E.
        cbn. congruence.
      * cbn in Ha0.
        rewrite even_false_mod2 in E.
        rewrite E.
        cbn. congruence.
    + lia_gsubst i 0.
      cbn. cbn in Ha0.
      congruence.
Qed.


Lemma mod2_0_1 n:
  n mod 2 = 0 \/
  n mod 2 = 1.
Proof.
  epose proof (mod_upper_bound n 2 _).
  Unshelve. 2: congruence.
  lia.
Qed.





Lemma divpow2r_pow2 i j:
  S j <= i ->
  divpow2r (2^i) j = 2^(i-S j).
Proof.
  intro H.
  gen i.
  induction j.
  - intros i H.
    destruct i as [|i]. 1: lia.
    rewrite pow2_1a,mul_comm,divpow2r_0.
    rewrite div_add_l. 2: congruence.
    cbn.
    rewrite sub_0_r,add_0_r.
    reflexivity.
  - intros i H.
    destruct i as [|i].
    1: lia.
    assert (S j <= i) by lia.
    specialize (IHj i H0).
    applys_eq IHj.
    replace (2^i) with (2^(S i)/2) by
      (rewrite pow2_1a,mul_comm,div_mul; congruence).
    rewrite divpow2r_div2.
    reflexivity.
Qed.

Lemma divpow2r_pow2sub1 i j:
  S j <= i ->
  divpow2r (2^i-1) j = 2^(i-S j).
Proof.
  intro H.
  gen i.
  induction j.
  - intros i H.
    destruct i as [|i]. 1: lia.
    rewrite pow2_1a,mul_comm,divpow2r_0.
    pose proof (pow2_nez i).
    replace (2^i*2-1+1) with (2^i*2) by lia.
    rewrite div_mul. 2: congruence. 
    f_equal. lia.
  - intros i H.
    destruct i as [|i].
    1: lia.
    assert (S j <= i) by lia.
    specialize (IHj i H0).
    applys_eq IHj.
    replace (2^i-1) with ((2^(S i)-1)/2). 2:{
      rewrite pow2_1a,mul_comm.
      pose proof (pow2_nez i).
      replace (2^i*2) with ((2^i-1+1)*2) by lia.
      rewrite mul_add_distr_r.
      rewrite <-add_sub_assoc. 2: lia.
      change (1*2-1) with 1%nat.
      rewrite div_add_l. 2: congruence.
      cbn. lia.
    }
    rewrite divpow2r_div2.
    reflexivity.
Qed.

Lemma divpow2r_small n i:
  n<2^i ->
  divpow2r n i = O.
Proof.
  intro H.
  unfold divpow2r.
  rewrite (add_comm i 1),pow2_1a.
  rewrite div_small; lia.
Qed.

Lemma divpow2r_pow2_small j i:
  j<i ->
  divpow2r (2^j) i = O.
Proof.
  intro H.
  apply divpow2r_small.
  apply pow_lt_mono_r; lia.
Qed.

Lemma divpow2r_pow2_1 j i:
  j=i ->
  divpow2r (2^j) i = S O.
Proof.
  intro H.
  unfold divpow2r.
  subst.
  rewrite (add_comm i 1),pow2_1a.
  replace (2^i+2^i) with (2*2^i) by lia.
  pose proof (pow2_nez i).
  rewrite div_same; lia.
Qed.

Lemma divpow2r_pow2sub1_small j i:
  j<=i ->
  divpow2r (2^j-1) i = O.
Proof.
  intro H.
  apply divpow2r_small.
  assert (j<i\/j=i) as E by lia.
  destruct E as [E|E].
  - pose proof (pow_lt_mono_r 2 j i).
    lia.
  - subst.
    pose proof (pow2_nez i).
    lia.
Qed.

Ltac simpl_divpow2r_pow2 H :=
  repeat (
  (rewrite divpow2r_pow2 in H; [idtac|lia]) ||
  (rewrite divpow2r_pow2_1 in H; [idtac|lia]) ||
  (rewrite divpow2r_pow2_small in H; [idtac|lia]) ||
  (rewrite divpow2r_pow2sub1 in H; [idtac|lia]) ||
  (rewrite divpow2r_pow2sub1_small in H; [idtac|lia])).


Lemma add_sub_c a b c:
  a+(S b)-(S c) = a+b-c.
Proof.
  lia.
Qed.

Lemma add_sub_c' a b c:
  a+(S b)-(a+(S c)) = a+b-(a+c).
Proof.
  lia.
Qed.

Lemma add_sub' a b:
  a+b-a = b.
Proof.
  lia.
Qed.


Ltac simpl_add_sub :=
  repeat (
  rewrite add_sub_c ||
  rewrite add_sub_c' ||
  rewrite add_sub' ||
  rewrite add_sub ||
  rewrite sub_0_r ||
  rewrite add_0_r ||
  rewrite add_0_l ||
  rewrite sub_diag ||
  rewrite sub_succ
).

Ltac simpl_add_sub_in H :=
  repeat (
  rewrite add_sub_c in H ||
  rewrite add_sub_c' in H ||
  rewrite add_sub' in H ||
  rewrite add_sub in H ||
  rewrite sub_0_r in H ||
  rewrite add_0_r in H ||
  rewrite add_0_l in H ||
  rewrite sub_diag in H ||
  rewrite sub_succ in H
).

Lemma ctz_upper_bound i m:
  m<2^i-1 ->
  ctzS m < i.
Proof.
  intro H.
  remember (ctzS m) as v1.
  symmetry in Heqv1.
  rewrite ctzS_spec in Heqv1.
  pose proof (Div0.mod_le m (2^(v1+1))) as H0.
  rewrite Heqv1 in H0.
  pose proof (pow2_nez v1) as H1.
  pose proof (pow2_nez i) as H2.
  assert (2^v1<2^i) as H3 by lia.
  rewrite <-pow_lt_mono_r_iff in H3; lia.
Qed.

Lemma ctzS_add i m:
  m<2^i-1 ->
  ctzS (2^i+m) = ctzS m.
Proof.
  intro H.
  pose proof (ctz_upper_bound i m H) as H0.
  remember (ctzS m) as v1.
  rewrite ctzS_spec.
  symmetry in Heqv1.
  rewrite ctzS_spec in Heqv1.
  rewrite <- Div0.add_mod_idemp_l.
  replace i with (i-(v1+1)+(v1+1)) by lia.
  rewrite pow_add_r.
  rewrite Div0.mod_mul.
  apply Heqv1.
Qed.

Lemma ctzS_sub i m:
  i>0 ->
  m<2^i-1 ->
  ctzS (2^i-m-2) = ctzS m.
Proof.
  intros Hi H.
  pose proof (ctz_upper_bound i m H) as H0.
  remember (ctzS m) as v1.
  rewrite ctzS_spec.
  symmetry in Heqv1.
  rewrite ctzS_spec in Heqv1.
  remember ((2^i-m-2) mod (2^(v1+1))) as v2.
  symmetry in Heqv2.
  pose proof (Div0.add_mod m 2 (2^(v1+1))) as H1.
  rewrite Heqv1 in H1.
  rewrite Div0.add_mod_idemp_r in H1.
  pose proof (Div0.add_mod (2^i-m-2) (m+2) (2^(v1+1))) as H2.
  rewrite Heqv2,H1 in H2.
  rewrite Div0.add_mod_idemp_r in H2.
  replace (2^i-m-2+(m+2)) with (2^i) in H2 by lia.
  replace i with (i-(v1+1)+(v1+1)) in H2 by lia.
  rewrite pow_add_r in H2.
  rewrite Div0.mod_mul in H2.
  assert (v2<2^v1-1\/v2=2^v1-1\/v2>2^v1-1) as E by lia.
  destruct E as [E|[E|E]].
  2: apply E.
  - rewrite mod_small in H2.
    2: rewrite (add_comm v1 1),pow2_1a; lia.
    lia.
  - pose proof (pow2_nez v1) as Hv1.
    replace (v2+(2^v1-1+2)) with ((v2-(2^v1-1))+2*2^v1) in H2 by lia.
    change (2*2^v1) with (2^(1+v1)) in H2.
    replace (2^(1+v1)) with (1*2^(1+v1)) in H2 by lia.
    rewrite (add_comm 1 v1) in H2.
    rewrite Div0.mod_add in H2.
    epose proof (mod_upper_bound (2^i-m-2) (2^(v1+1)) _) as H3.
    Unshelve. 2: pose proof (pow2_nez (v1+1)); lia.
    rewrite Heqv2 in H3.
    rewrite mod_small in H2; lia.
Qed.

Section Sk.

Hypothesis k:nat.
Hypothesis Base_k: k<>0.

Inductive Base: (nat*(list nat))->Prop :=
| Base_intro s
  (Base_a0':fst s = S O)
  (Base_a:forall i, ai i s = if Nat.ltb i (k*2) then 2^(k*2-i) else O)
  (Base_l:to_l s = k*2+1):
  Base s.

Lemma Base_embanked {s1}:
  Base s1 ->
  exists s7 s_1 s_2,
    embanked s1 s7 s_1 (2^(k*2)-1) s_2 (2^(k*2)) /\
    (Add2 (k*2+1) s1 s7).
Proof.
  intro HB.
  inversion HB; subst.
  assert (H_l:to_l s1 >= 3) by lia.
  destruct s1 as [x xs].
  cbn in Base_a0'.
  subst x.
  assert (Ha0_odd:Odd (fst (1%nat,xs))). {
    cbn.
    rewrite <-odd_spec.
    reflexivity.
  }
  assert (Ha1:ai O (1%nat,xs) = 2^(k*2)). {
    rewrite (Base_a O).
    destruct (Nat.ltb_spec O (k*2)) as [E|E]. 2: lia.
    f_equal. apply sub_0_r.
  }
  assert (Ha2:ai 1 (1%nat,xs) = 2^(k*2-1)). {
    rewrite (Base_a 1%nat).
    destruct (Nat.ltb_spec 1 (k*2)) as [E|E]. 2: lia.
    reflexivity.
  }
  assert (Ha0_lt:fst (1%nat,xs) < 2 ^ to_l (1%nat,xs) - 1). {
    rewrite Base_l. cbn.
    destruct k as [|k']. 1: congruence.
    cbn.
    pose proof (pow2_nez (k'*2+1)).
    lia.
  }
  pose proof Base_l as Base_l'.
  cbn in Base_l.
  rewrite grey_to_binary_length,length_map in Base_l.
  assert (Hxsnn:xs<>[]) by (intro X; rewrite X in Base_l; cbn in Base_l; lia).
  destruct (exists_last Hxsnn) as [xs0 [x1 Hxs]].
  subst xs.
  rewrite length_app in Base_l. cbn in Base_l.
  assert (Hl:length xs0 = k*2) by lia.
  assert (Hx1:x1=O). {
    specialize (Base_a (k*2)).
    destruct (Nat.ltb_spec (k*2) (k*2)) as [E|E].
    1: lia.
    cbn in Base_a.
    rewrite app_nth2 in Base_a. 2: lia.
    replace (k*2-length xs0) with O in Base_a by lia.
    cbn in Base_a.
    apply Base_a.
  }
  subst x1.
  assert (H_ev:Forall Even xs0). {
    rewrite Forall_forall.
    intros x HIn.
    destruct (In_nth _ _ O HIn) as [i [H0 H1]].
    specialize (Base_a i).
    unfold ai,snd in Base_a.
    rewrite app_nth1 in Base_a. 2: auto 1.
    rewrite H1 in Base_a.
    destruct (Nat.ltb_spec i (k*2)) as [E|E]. 2: lia.
    subst x.
    replace (k*2-i) with (1+(k*2-i-1)) by lia.
    rewrite pow2_1a.
    econstructor. reflexivity.
  }
  assert (H_nz:Forall Nonzero xs0). {
    rewrite Forall_forall.
    intros x HIn.
    destruct (In_nth _ _ O HIn) as [i [H0 H1]].
    specialize (Base_a i).
    unfold ai,snd in Base_a.
    rewrite app_nth1 in Base_a. 2: auto 1.
    rewrite H1 in Base_a.
    destruct (Nat.ltb_spec i (k*2)) as [E|E]. 2: lia.
    subst x.
    apply (pow2_nez (k*2-i)).
  }
  assert (H_wf1:WF1 (1%nat,xs0++[O])) by (econstructor; eauto 1).
  assert (H_n:to_n (1%nat,xs0++[O]) = O). {
    apply to_n_Even.
    rewrite Forall_app.
    split; auto 2.
  }
  assert (H_s:to_s (1%nat,xs0++[O]) = false). {
    cbn.
    simpl_list_to_binary_0s.
    reflexivity.
  }
  assert (H_a1_lt:ai 0 (1%nat,xs0++[O]) < 3 * 2 ^ (to_l (1%nat,xs0++[O]) - 1)). {
    remember (to_l (1%nat, xs0 ++ [O])) as l1.
    specialize (Base_a O).
    rewrite Base_a.
    destruct (Nat.ltb_spec O (k*2)) as [E|E]. 2: lia.
    rewrite Base_l'.
    replace (k*2+1-1) with (k*2) by lia.
    rewrite sub_0_r.
    pose proof (pow2_nez (k*2)).
    lia.
  }
  eassert (Hwemb:_) by
    (eapply weakly_embanked_precond with (s1:=(1%nat,xs0++[O])); eassumption).
  destruct Hwemb as [s6 [s_1 [h_1 [s_2 [h_2 Hwemb]]]]].
  inversion Hwemb; subst.
  rewrite Base_l' in n3_expr,n4_expr,n5_expr,n6_expr,a60_expr.
  rewrite Ha1 in n5_expr,n6_expr.
  rewrite Ha2 in a60_expr.
  unfold fst in n3_expr,n4_expr,n5_expr,n6_expr.
  rewrite add_0_r in n4_expr.
  rewrite add_sub in n4_expr,n5_expr.
  replace (k*2+1-2) with (k*2-1) in n6_expr,a60_expr by lia.
  rewrite pow2_div2 in n6_expr. 2: lia.
  rewrite pow2_add in n5_expr,n6_expr,a60_expr.
  replace (k*2-1+1) with (k*2) in n6_expr,a60_expr by lia.
  rewrite pow2_sub1 in n3_expr,n4_expr.
  rewrite n3_expr,n4_expr,n5_expr in a60_expr.
  do 2 rewrite divpow2r_0 in a60_expr.
  rewrite sub_add in a60_expr. 2: pose proof (pow2_nez (k*2)); lia.
  rewrite div2ceil_div2floor_Even in a60_expr. 2: apply pow2_Even; lia.
  do 2 (rewrite pow2_div2 in a60_expr; [idtac | lia]).
  rewrite add_sub in a60_expr.
  unfold divpow2r in a60_expr.
  change (2^1) with 2 in a60_expr.
  change (2^(1+1)) with (2*2) in a60_expr.
  replace (2^(k*2+1)-1+2) with (2^(k*2+1)+1) in a60_expr by (pose proof (pow2_nez (k*2+1)); lia).
  rewrite <-Div0.div_div in a60_expr.
  rewrite div2ceil_div2floor_Even in a60_expr. 2: apply pow2_Even; lia.
  do 2 (rewrite pow2_div2 in a60_expr; [idtac | lia]).
  rewrite add_sub in a60_expr.
  rewrite pow2_add in a60_expr.
  rewrite <-add_assoc in a60_expr.
  rewrite pow2_add in a60_expr.
  rewrite sub_add in a60_expr. 2: lia.
  rewrite (add_comm (k*2) 1) in a60_expr.
  rewrite pow2_1a in a60_expr.
  assert (a60_expr':fst s6 = 2^(k*2)+1) by lia.
  clear a60_expr. rename a60_expr' into a60_expr.
  eassert (Hemb:_). {
    eapply embanked_precond.
    - apply Hwemb.
    - lia.
  }
  destruct Hemb as [s7 Hemb].
  inversion Hemb. subst s1' s7' s_1' h_1' s_2' h_2'.
  rewrite n3_expr,n4_expr,n5_expr,n6_expr,Base_l' in a7_expr,a70_expr.

  assert (Hadd:(Add2 (k*2+1) (1,xs0++[0]) s7)%nat). {
    constructor.
    intro i.
    destruct i as [|i].
    - unfold ai'.
      destruct (Nat.eqb_spec 0 (k*2)) as [E|E].
      1: lia.
      simpl_divpow2r_pow2 a70_expr.
      rewrite Hs7n in a70_expr.
      rewrite Base_a in a70_expr.
      destruct (Nat.ltb_spec (S O) (k*2)) as [E1|E1]. 2: lia.
      destruct (Nat.eqb_spec (O) (k*2+1)) as [E2|E2]. 1: lia.
      rewrite add_sub in a70_expr.
      assert (H:fst s7 = S O) by lia.
      rewrite H.
      reflexivity.
    - unfold ai'.
      specialize (a7_expr i).
      destruct (Nat.eqb_spec (S i) (k*2+1)) as [E|E].
      + simpl_divpow2r_pow2 a7_expr.
        destruct (Nat.eqb_spec (S (S i)) (k*2 + 1 - 1)) as [E0|E0]. 1: lia.
        rewrite Base_a in a7_expr.
        destruct (Nat.ltb_spec (S(S i)) (k*2)) as [E1|E1]. 1: lia.
        rewrite Base_a.
        destruct (Nat.ltb_spec (i) (k*2)) as [E2|E2]. 1: lia.
        lia.
      + assert (i<k*2\/k*2<i) as [E0|E0] by lia.
        * simpl_divpow2r_pow2 a7_expr.
          rewrite Base_a.
          destruct (Nat.ltb_spec (i) (k*2)) as [E1'|E1']. 2: lia.
        assert (i+1=k*2\/i+1<k*2) as [E1|E1] by lia.
        -- simpl_divpow2r_pow2 a7_expr.
          destruct (Nat.eqb_spec (S (S i)) (k*2 + 1 - 1)) as [E2|E2]. 1: lia.
          rewrite <-E1 in a7_expr.
          repeat rewrite (add_comm _ 1) in a7_expr.
          repeat rewrite sub_diag in a7_expr.
          rewrite Base_a in a7_expr.
          destruct (Nat.ltb_spec (S(S i)) (k*2)) as [E3|E3]. 1: lia.
          replace (k*2-i) with 1%nat by lia.
          cbn.
          cbn in a7_expr.
          lia.
        -- simpl_divpow2r_pow2 a7_expr.
          assert (i+2=k*2\/i+2<k*2) as [E2|E2] by lia.
        ++ destruct (Nat.eqb_spec (S (S i)) (k*2 + 1 - 1)) as [E3|E3]. 2: lia.
          replace (k*2-(S(S i))) with O in a7_expr by lia.
          replace (k*2-((S i))) with (S O) in a7_expr by lia.
          replace (k*2+1-(S(S i))) with (S O) in a7_expr by lia.
          replace (k*2+1-(S(S(S i)))) with (O) in a7_expr by lia.
          rewrite Base_a in a7_expr.
          destruct (Nat.ltb_spec (S(S i)) (k*2)) as [E4|E4]. 1: lia.
          replace (k*2-i) with 2 by lia.
          cbn. cbn in a7_expr. lia.
        ++ destruct (Nat.eqb_spec (S (S i)) (k*2 + 1 - 1)) as [E3|E3]. 1: lia.
          rewrite Base_a in a7_expr.
          destruct (Nat.ltb_spec (S(S i)) (k*2)) as [E4|E4]. 2: lia.
          replace (k*2+1-S(S i)) with (k*2-S i) in a7_expr by lia.
          assert (ai i s7 = 2*2^(k*2-S i)) as H by lia.
          replace (k*2-i) with (1+(k*2-S i)) by lia.
          rewrite pow2_1a.
          lia.
        * simpl_divpow2r_pow2 a7_expr.
          destruct (Nat.eqb_spec (S (S i)) (k*2 + 1 - 1)) as [E1|E1]. 1: lia.
          rewrite Base_a in a7_expr.
          destruct (Nat.ltb_spec (S(S i)) (k*2)) as [E2|E2]. 1: lia.
          rewrite Base_a.
          destruct (Nat.ltb_spec (i) (k*2)) as [E3|E3]. 1: lia.
          lia.
  }
  rewrite n4_expr,n6_expr in Hemb.
  do 3 eexists; split.
  - apply Hemb.
  - apply Hadd.
Qed.


Lemma Base_embanked_batch {e}:
  Base e ->
  exists ne,
  embanked_batch (k*2+1) e ne (2^(k*2)-1) (2^(k*2)) /\
  to_l ne = k*2+1 /\
  ai' 0 ne = 1 /\
  ai' 1 ne = 2^(k*2)+2 /\
  Add2s (k*2+1) e ne.
Proof.
  intro HB.
  destruct (Base_embanked HB) as [ne0 [s_1 [s_2 [He Ha]]]].
  destruct (embanked__embanked_batch He Ha) as [ne Hne].
  inverts HB.
  destruct (embanked_batch_a0_a1 Hne) as [Ha0 Ha1].
  epose proof (embanked_batch_Add2s Hne).
  exists ne.
  rsplit; auto 1.
  - pose proof (embanked_batch_len Hne).
    congruence.
  - cbn.
    clear Base_l.
    lia_gsubst (k*2+1) (1+k*2).
    rewrite Div0.mod_add in Ha0.
    cbn in Ha0.
    lia.
  - cbn.
    clear Base_l.
    lia_gsubst (k*2+1) (1+k*2).
    rewrite Div0.mod_add in Ha1.
    cbn in Ha1.
    specialize (Base_a 0).
    destruct (Nat.ltb_spec 0 (k*2)). 2: lia.
    rewrite sub_0_r in Base_a.
    lia.
Qed.

Lemma embanked_batch_precond'' {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  to_l ne = k*2+1 ->
  ai' 0 ne < 2^(k*2)*2 - 1 ->
  ai' 1 ne < 2^(k*2)*3 ->
  exists n'ne,
  match i mod 2 with
  | 0 => embanked_batch (ctzS (h_1-1)) ne n'ne (h_1-1) h_2
  | 1 => embanked_batch (S (ctzS h_2)) ne n'ne h_1 (h_2+1)
  | _ => False
  end.
Proof.
  intros.
  replace (2^(k*2)*2) with (2^(k*2+1)) in H1 by (apply pow_add_r).
  eapply embanked_batch_precond'; eauto 1.
  - congruence.
  - rewrite H0,add_sub.
    congruence.
Qed.

Lemma mod2_1_S a:
  a mod 2 = 1 <-> (S a) mod 2 = 0.
Proof.
  rewrite <-even_true_mod2.
  rewrite <-even_false_mod2.
  simpl_oe_S.
  unfold odd.
  simpl_xor_neg.
Qed.

Lemma mod2_0_S a:
  a mod 2 = 0 <-> (S a) mod 2 = 1.
Proof.
  rewrite <-even_true_mod2.
  rewrite <-even_false_mod2.
  simpl_oe_S.
  unfold odd.
  simpl_xor_neg.
Qed.

Ltac pose_Heb Heb Hl e2 Heb2 rw :=
  epose proof (embanked_batch_precond'' Heb Hl _ _) as tmp;
  edestruct tmp as [e2 Heb2]; clear tmp;
  rewrite rw in Heb2;
  cbn in Heb2.

Ltac ex_Heb e Heb :=
  exists e; eexists;
  split;
  [ apply Heb | idtac ].

Ltac pose_eb_len Heb Hl0 Hl :=
  pose proof (embanked_batch_len Heb) as Hl;
  rewrite Hl0 in Hl; symmetry in Hl.

Ltac pose_eb_a0_a1 Heb Ha0 Ha1 rw :=
  destruct (embanked_batch_a0_a1 Heb) as [Ha0 Ha1];
  rewrite rw in Ha0,Ha1;
  cbn in Ha0,Ha1.


Lemma mod_mod' a b c:
  a mod c = a mod (b*c) mod c.
Proof.
  rewrite (Div0.div_mod a (b*c)).
  rewrite <-Div0.add_mod_idemp_l.
  rewrite mul_comm,mul_assoc,Div0.mod_mul.
  cbn.
  rewrite <-mul_assoc.
  rewrite <-Div0.add_mod_idemp_l.
  rewrite Div0.mod_mul.
  cbn.
  rewrite Div0.mod_mod.
  reflexivity.
Qed.

Lemma le_ctzS_sum i m:
  2*(m/(2^i)) + (if i <=? ctzS m then 2 else 0) = 2*((m+1)/(2^i)).
Proof.
  destruct (Nat.leb_spec i (ctzS m)) as [E|E].
  - remember (ctzS m) as v1.
    symmetry in Heqv1.
    pose proof Heqv1 as Heqv1'.
    rewrite ctzS_spec in Heqv1.
    assert (m mod 2^i = 2^i-1). {
      replace (v1+1) with (v1+1-i+i) in Heqv1 by lia.
      rewrite pow_add_r in Heqv1.
      rewrite (mod_mod' m (2^(v1+1-i)) (2^i)).
      rewrite Heqv1.
      replace v1 with (v1-i+i) by lia.
      rewrite pow_add_r.
      pose proof (pow2_nez (v1-i)).
      pose proof (pow2_nez i).
      replace (2^(v1-i)) with (2^(v1-i)-1+1) by lia.
      rewrite mul_add_distr_r.
      rewrite mul_1_l.
      rewrite <-add_sub_assoc.
      2: lia.
      rewrite add_comm,Div0.mod_add.
      rewrite mod_small; lia.
    }
    pose proof (Div0.div_mod m (2^i)) as H0.
    rewrite H in H0.
    rewrite H0.
    rewrite (mul_comm (2^i)).
    pose proof (pow2_nez i) as Hpi.
    rewrite div_add_l. 2: lia.
    rewrite <-add_assoc.
    rewrite div_add_l. 2: lia.
    rewrite (div_small (2^i-1)). 2: lia.
    rewrite sub_add. 2: lia.
    rewrite div_same. 2: lia.
    lia.
  - remember (ctzS m) as v1.
    symmetry in Heqv1.
    pose proof Heqv1 as Heqv1'.
    rewrite ctzS_spec in Heqv1.
    pose proof (pow2_nez i) as Hpi.
    pose proof (pow2_nez v1) as Hpv1.
    assert (2^v1<2^i) as Hplt by (rewrite <-pow_lt_mono_r_iff; lia).

    rewrite (Div0.div_mod m (2^(i))).
    rewrite (mul_comm (2^i)).
    rewrite div_add_l. 2: lia.
    rewrite <-add_assoc.
    rewrite div_add_l. 2: lia.
    rewrite add_0_r.
    f_equal.
    f_equal.


    rewrite (Div0.div_mod m (2^(v1+1))).
    rewrite Heqv1.
    replace (i) with (i-(v1+1)+(v1+1)) by lia.
    rewrite (pow_add_r 2 (i-(v1+1)) (v1+1)).
    rewrite (mul_comm (2^(v1+1))).
    rewrite Div0.add_mul_mod_distr_r.
    2: rewrite add_comm,pow2_1a; lia.
    rewrite (mul_comm (2^(i-(v1+1))) (2^(v1+1))).
    do 2 rewrite <-Div0.div_div.
    rewrite div_add_l. 2: apply pow2_nez.
    rewrite <-add_assoc.
    rewrite div_add_l. 2: apply pow2_nez.
    f_equal.
    f_equal.
    rewrite div_small.
    2: rewrite add_comm,pow2_1a; lia.
    rewrite div_small.
    2: rewrite (add_comm v1 1),pow2_1a; lia.
    reflexivity.
Qed.

Lemma Nat_leb_S a b:
  (Nat.leb (S a) (S b)) = (Nat.leb a b).
Proof.
  reflexivity.
Qed.

Lemma Nat_leb_S_l a b:
  even (S a) = even b ->
  (Nat.leb (S a) b) = (Nat.leb a b).
Proof.
  intro H.
  destruct (Nat.leb_spec a b).
  - destruct (Nat.leb_spec (S a) b); auto 1.
    assert (a=b) by lia. subst.
    rewrite even_succ in H.
    unfold odd in H.
    destruct (even b); cbn in H; congruence.
  - destruct (Nat.leb_spec (S a) b); auto 1.
    lia.
Qed.

Lemma Nat_leb_S_r a b:
  even a = even b ->
  (Nat.leb a (S b)) = (Nat.leb a b).
Proof.
  intro H.
  destruct (Nat.leb_spec a b).
  - destruct (Nat.leb_spec a (S b)); auto 1. lia.
  - destruct (Nat.leb_spec a (S b)); auto 1.
    assert (a=S b) by lia. subst.
    rewrite even_succ in H.
    unfold odd in H.
    destruct (even b); cbn in H; congruence.
Qed.

Ltac simpl_Add2s :=
  unfold ai';
  cbn[negb]; cbn[Bool.eqb];
  repeat rewrite Bool.andb_true_r;
  repeat rewrite Bool.andb_false_r;
  repeat (rewrite Nat_leb_S);
  repeat (rewrite Nat_leb_S_l; [idtac|congruence]).

Ltac inv_eb_Add2s Heb := pose proof (embanked_batch_Add2s Heb) as tmp; inverts tmp.


(* case of Proposition 4.1 *)
Lemma embanked_4batch m i0 e0 e1:
  m+3 < 2^(k*2) ->
  ctzS m mod 2 = 0 ->
  ctzS (m+1) mod 2 = 1 ->

  embanked_batch i0 e0 e1 (2^(k*2)-1-m) (2^(k*2)+m) ->
  i0 mod 2 = 1 ->
  to_l e1 = k*2+1 ->
  ai' 0 e1 = 1+m*2 ->
  ai' 1 e1 = 2^(k*2)+2+m*2 ->

  exists e2 i2,
  embanked_batch i2 e1 e2 (2^(k*2)-1-(m)) (2^(k*2)+(m+1)) /\

  exists e3 i3,
  embanked_batch i3 e2 e3 (2^(k*2)-1-(m)) (2^(k*2)+(m+2)) /\

  exists e4 i4,
  embanked_batch i4 e3 e4 (2^(k*2)-1-(m+1)) (2^(k*2)+(m+2)) /\

  exists e5 i5,
  embanked_batch i5 e4 e5 (2^(k*2)-1-(m+2)) (2^(k*2)+(m+2)) /\

  i5 mod 2 = 1 /\
  to_l e5 = k*2+1 /\
  ai' 0 e5 = 1+(m+2)*2 /\
  ai' 1 e5 = 2^(k*2)+2+(m+2)*2 /\
  (forall i, ai i e5 + 2*(m/2^i) = ai i e1 + 2*((m+2)/2^i))
.
Proof.
  intros Hm_lt Hc0' Hc1'.

  assert (Hc0a:ctzS (2^(k*2)+m) = ctzS m) by (rewrite ctzS_add; lia).
  assert (Hc1a:ctzS (2^(k*2)+(m+1)) = ctzS (m+1)) by (rewrite ctzS_add; lia).
  assert (Hc2a:ctzS (2^(k*2)-1-(m+1)) = ctzS m). {
    replace (2^(k*2)-1-(m+1)) with (2^(k*2)-(m)-2) by lia.
    rewrite ctzS_sub; lia.
  }
  assert (Hc3a:ctzS (2^(k*2)-1-(m+2)) = ctzS (m+1)). {
    replace (2^(k*2)-1-(m+2)) with (2^(k*2)-(m+1)-2) by lia.
    rewrite ctzS_sub; lia.
  }
  pose proof Hc0' as Hc0.
  pose proof Hc1' as Hc1.
  pose proof Hc0' as Hc3.
  pose proof Hc1' as Hc4.
  rewrite <-Hc0a in Hc0.
  rewrite <-Hc1a in Hc1.
  rewrite <-Hc2a in Hc3.
  rewrite <-Hc3a in Hc4.

  intros Heb1 Hi1 Hl1 Ha10 Ha11.
  cbn in Ha10,Ha11.

  rewrite mod2_0_S in Hc0.
  rewrite mod2_1_S in Hc1.


  pose_Heb Heb1 Hl1 e2 Heb2 Hi1.
  replace (2^(k*2)+m+1) with (2^(k*2)+(m+1)) in Heb2 by lia.
  ex_Heb e2 Heb2.

  pose_eb_len Heb2 Hl1 Hl2.
  pose_eb_a0_a1 Heb2 Ha20 Ha21 Hc0.


  pose_Heb Heb2 Hl2 e3 Heb3 Hc0.
  cbn in Heb3.
  replace (2^(k*2)+(m+1)+1) with (2^(k*2)+(m+2)) in Heb3 by lia.
  ex_Heb e3 Heb3.

  pose_eb_len Heb3 Hl2 Hl3.
  pose_eb_a0_a1 Heb3 Ha30 Ha31 Hc1.


  pose_Heb Heb3 Hl3 e4 Heb4 Hc1.
  replace (2^(k*2)-1-m-1) with (2^(k*2)-1-(m+1)) in Heb4 by lia.
  ex_Heb e4 Heb4.

  pose_eb_len Heb4 Hl3 Hl4.
  pose_eb_a0_a1 Heb4 Ha40 Ha41 Hc3.


  pose_Heb Heb4 Hl4 e5 Heb5 Hc3.
  replace (2^(k*2)-1-(m+1)-1) with (2^(k*2)-1-(m+2)) in Heb5 by lia.
  ex_Heb e5 Heb5.

  pose_eb_len Heb5 Hl4 Hl5.
  pose_eb_a0_a1 Heb5 Ha50 Ha51 Hc4.

  assert (Ha:forall i, ai i e5 + 2*((m)/2^i) = ai i e1 + 2*((m+2)/2^i)). {
    inv_eb_Add2s Heb2.
    inv_eb_Add2s Heb3.
    inv_eb_Add2s Heb4.
    inv_eb_Add2s Heb5.

    intro i.
    specialize (Hadd2s (S i)).
    specialize (Hadd2s0 (S i)).
    specialize (Hadd2s1 (S i)).
    specialize (Hadd2s2 (S i)).
    rewrite Hc0a in Hadd2s.
    rewrite Hc1a in Hadd2s0.
    rewrite Hc2a in Hadd2s1.
    rewrite Hc3a in Hadd2s2.
    rewrite <-even_true_mod2 in Hc0'.
    rewrite <-even_false_mod2 in Hc1'.
    destruct (even (S i)) eqn:E;
      gen Hadd2s Hadd2s0 Hadd2s1 Hadd2s2;
      simpl_oe_S;
      unfold odd;
      rewrite Hc0',Hc1';
      simpl_Add2s;
      pose proof (le_ctzS_sum i m) as H;
      pose proof (le_ctzS_sum i (m+1)) as H0;
      replace (m+1+1) with (m+2) in H0 by lia;
      lia.
  }

  rewrite Hc4.
  repeat split.
  - congruence.
  - cbn. lia.
  - cbn. lia.
  - apply Ha.


  Unshelve.
  all: cbn; lia.
Qed.


(* case of Proposition 4.1 *)
Lemma embanked_8batch m i0 e0 e1:
  m+5 < 2^(k*2) ->
  ctzS m mod 2 = 0 ->
  ctzS (m+1) mod 2 = 0 ->
  ctzS (m+2) mod 2 = 0 ->
  ctzS (m+3) mod 2 = 1 ->

  embanked_batch i0 e0 e1 (2^(k*2)-1-m) (2^(k*2)+m) ->
  i0 mod 2 = 1 ->
  to_l e1 = k*2+1 ->
  ai' 0 e1 = 1+m*2 ->
  ai' 1 e1 = 2^(k*2)+2+m*2 ->

  exists e2 i2,
  embanked_batch i2 e1 e2 (2^(k*2)-1-(m)) (2^(k*2)+(m+1)) /\

  exists e3 i3,
  embanked_batch i3 e2 e3 (2^(k*2)-1-(m)) (2^(k*2)+(m+2)) /\

  exists e4 i4,
  embanked_batch i4 e3 e4 (2^(k*2)-1-(m)) (2^(k*2)+(m+3)) /\

  exists e5 i5,
  embanked_batch i5 e4 e5 (2^(k*2)-1-(m)) (2^(k*2)+(m+4)) /\

  exists e6 i6,
  embanked_batch i6 e5 e6 (2^(k*2)-1-(m+1)) (2^(k*2)+(m+4)) /\

  exists e7 i7,
  embanked_batch i7 e6 e7 (2^(k*2)-1-(m+2)) (2^(k*2)+(m+4)) /\

  exists e8 i8,
  embanked_batch i8 e7 e8 (2^(k*2)-1-(m+3)) (2^(k*2)+(m+4)) /\

  exists e9 i9,
  embanked_batch i9 e8 e9 (2^(k*2)-1-(m+4)) (2^(k*2)+(m+4)) /\

  i9 mod 2 = 1 /\
  to_l e9 = k*2+1 /\
  ai' 0 e9 = 1+(m+4)*2 /\
  ai' 1 e9 = 2^(k*2)+2+(m+4)*2 /\
  (forall i, ai i e9 + 2*(m/2^i) = ai i e1 + 2*((m+4)/2^i))
.
Proof.
  intros Hm_lt Hc0' Hc1' Hc2' Hc3'.

  assert (Hc0a:ctzS (2^(k*2)+m) = ctzS m) by (rewrite ctzS_add; lia).
  assert (Hc1a:ctzS (2^(k*2)+(m+1)) = ctzS (m+1)) by (rewrite ctzS_add; lia).
  assert (Hc2a:ctzS (2^(k*2)+(m+2)) = ctzS (m+2)) by (rewrite ctzS_add; lia).
  assert (Hc3a:ctzS (2^(k*2)+(m+3)) = ctzS (m+3)) by (rewrite ctzS_add; lia).
  assert (Hc4a:ctzS (2^(k*2)-1-(m+1)) = ctzS m). {
    replace (2^(k*2)-1-(m+1)) with (2^(k*2)-(m)-2) by lia.
    rewrite ctzS_sub; lia.
  }
  assert (Hc5a:ctzS (2^(k*2)-1-(m+2)) = ctzS (m+1)). {
    replace (2^(k*2)-1-(m+2)) with (2^(k*2)-(m+1)-2) by lia.
    rewrite ctzS_sub; lia.
  }
  assert (Hc6a:ctzS (2^(k*2)-1-(m+3)) = ctzS (m+2)). {
    replace (2^(k*2)-1-(m+3)) with (2^(k*2)-(m+2)-2) by lia.
    rewrite ctzS_sub; lia.
  }
  assert (Hc7a:ctzS (2^(k*2)-1-(m+4)) = ctzS (m+3)). {
    replace (2^(k*2)-1-(m+4)) with (2^(k*2)-(m+3)-2) by lia.
    rewrite ctzS_sub; lia.
  }
  pose proof Hc0' as Hc0.
  pose proof Hc1' as Hc1.
  pose proof Hc2' as Hc2.
  pose proof Hc3' as Hc3.
  pose proof Hc0' as Hc5.
  pose proof Hc1' as Hc6.
  pose proof Hc2' as Hc7.
  pose proof Hc3' as Hc8.
  rewrite <-Hc0a in Hc0.
  rewrite <-Hc1a in Hc1.
  rewrite <-Hc2a in Hc2.
  rewrite <-Hc3a in Hc3.
  rewrite <-Hc4a in Hc5.
  rewrite <-Hc5a in Hc6.
  rewrite <-Hc6a in Hc7.
  rewrite <-Hc7a in Hc8.


  intros Heb1 Hi1 Hl1 Ha10 Ha11.
  cbn in Ha10,Ha11.

  rewrite mod2_0_S in Hc0.
  rewrite mod2_0_S in Hc1.
  rewrite mod2_0_S in Hc2.
  rewrite mod2_1_S in Hc3.


  pose_Heb Heb1 Hl1 e2 Heb2 Hi1.
  replace (2^(k*2)+m+1) with (2^(k*2)+(m+1)) in Heb2 by lia.
  ex_Heb e2 Heb2.

  pose_eb_len Heb2 Hl1 Hl2.
  pose_eb_a0_a1 Heb2 Ha20 Ha21 Hc0.


  pose_Heb Heb2 Hl2 e3 Heb3 Hc0.
  cbn in Heb3.
  replace (2^(k*2)+(m+1)+1) with (2^(k*2)+(m+2)) in Heb3 by lia.
  ex_Heb e3 Heb3.

  pose_eb_len Heb3 Hl2 Hl3.
  pose_eb_a0_a1 Heb3 Ha30 Ha31 Hc1.


  pose_Heb Heb3 Hl3 e4 Heb4 Hc1.
  replace (2^(k*2)+(m+2)+1) with (2^(k*2)+(m+3)) in Heb4 by lia.
  ex_Heb e4 Heb4.

  pose_eb_len Heb4 Hl3 Hl4.
  pose_eb_a0_a1 Heb4 Ha40 Ha41 Hc2.


  pose_Heb Heb4 Hl4 e5 Heb5 Hc2.
  replace (2^(k*2)+(m+3)+1) with (2^(k*2)+(m+4)) in Heb5 by lia.
  ex_Heb e5 Heb5.

  pose_eb_len Heb5 Hl4 Hl5.
  pose_eb_a0_a1 Heb5 Ha50 Ha51 Hc3.


  pose_Heb Heb5 Hl5 e6 Heb6 Hc3.
  replace (2^(k*2)-1-m-1) with (2^(k*2)-1-(m+1)) in Heb6 by lia.
  ex_Heb e6 Heb6.

  pose_eb_len Heb6 Hl5 Hl6.
  pose_eb_a0_a1 Heb6 Ha60 Ha61 Hc5.


  pose_Heb Heb6 Hl6 e7 Heb7 Hc5.
  replace (2^(k*2)-1-(m+1)-1) with (2^(k*2)-1-(m+2)) in Heb7 by lia.
  ex_Heb e7 Heb7.

  pose_eb_len Heb7 Hl6 Hl7.
  pose_eb_a0_a1 Heb7 Ha70 Ha71 Hc6.


  pose_Heb Heb7 Hl7 e8 Heb8 Hc6.
  replace (2^(k*2)-1-(m+2)-1) with (2^(k*2)-1-(m+3)) in Heb8 by lia.
  ex_Heb e8 Heb8.

  pose_eb_len Heb8 Hl7 Hl8.
  pose_eb_a0_a1 Heb8 Ha80 Ha81 Hc7.


  pose_Heb Heb8 Hl8 e9 Heb9 Hc7.
  replace (2^(k*2)-1-(m+3)-1) with (2^(k*2)-1-(m+4)) in Heb9 by lia.
  ex_Heb e9 Heb9.

  pose_eb_len Heb9 Hl8 Hl9.
  pose_eb_a0_a1 Heb9 Ha90 Ha91 Hc8.

  assert (Ha:forall i, ai i e9 + 2*((m)/2^i) = ai i e1 + 2*((m+4)/2^i)). {
    inv_eb_Add2s Heb2.
    inv_eb_Add2s Heb3.
    inv_eb_Add2s Heb4.
    inv_eb_Add2s Heb5.
    inv_eb_Add2s Heb6.
    inv_eb_Add2s Heb7.
    inv_eb_Add2s Heb8.
    inv_eb_Add2s Heb9.

    intro i.
    specialize (Hadd2s (S i)).
    specialize (Hadd2s0 (S i)).
    specialize (Hadd2s1 (S i)).
    specialize (Hadd2s2 (S i)).
    specialize (Hadd2s3 (S i)).
    specialize (Hadd2s4 (S i)).
    specialize (Hadd2s5 (S i)).
    specialize (Hadd2s6 (S i)).
    rewrite Hc0a in Hadd2s.
    rewrite Hc1a in Hadd2s0.
    rewrite Hc2a in Hadd2s1.
    rewrite Hc3a in Hadd2s2.
    rewrite Hc4a in Hadd2s3.
    rewrite Hc5a in Hadd2s4.
    rewrite Hc6a in Hadd2s5.
    rewrite Hc7a in Hadd2s6.
    rewrite <-even_true_mod2 in Hc0',Hc1',Hc2'.
    rewrite <-even_false_mod2 in Hc3'.
    destruct (even (S i)) eqn:E;
      gen Hadd2s Hadd2s0 Hadd2s1 Hadd2s2 Hadd2s3 Hadd2s4 Hadd2s5 Hadd2s6;
      simpl_oe_S;
      unfold odd;
      rewrite Hc0',Hc1',Hc2',Hc3';
      simpl_Add2s;
      pose proof (le_ctzS_sum i m) as H;
      pose proof (le_ctzS_sum i (m+1)) as H0;
      pose proof (le_ctzS_sum i (m+2)) as H1;
      pose proof (le_ctzS_sum i (m+3)) as H2;
      replace (m+1+1) with (m+2) in H0 by lia;
      replace (m+2+1) with (m+3) in H1 by lia;
      replace (m+3+1) with (m+4) in H2 by lia;
      lia.
  }


  rewrite Hc8.
  repeat split.
  - congruence.
  - cbn. lia.
  - cbn. lia.
  - apply Ha.


  Unshelve.
  all: cbn; lia.
Qed.




Inductive ctzS_chain:nat->Prop :=
| ctzS_chain_O:
  ctzS_chain O
| ctzS_chain_S2 n:
  ctzS_chain n ->
  ctzS n mod 2 = 0 ->
  ctzS (n+1) mod 2 = 1 ->
  ctzS_chain (n+2)
| ctzS_chain_S4 n:
  ctzS_chain n ->
  ctzS n mod 2 = 0 ->
  ctzS (n+1) mod 2 = 0 ->
  ctzS (n+2) mod 2 = 0 ->
  ctzS (n+3) mod 2 = 1 ->
  ctzS_chain (n+4)
.

Lemma ctzS_even_0 n:
  n mod 2 = 0 ->
  ctzS n = 0.
Proof.
  intro H.
  rewrite ctzS_spec.
  apply H.
Qed.

Lemma ctzS_mod4eq1 n:
  n mod 4 = 1 ->
  ctzS n = 1.
Proof.
  intro H.
  rewrite ctzS_spec.
  apply H.
Qed.

Lemma ctzS_odd_odd n:
  ctzS n mod 2 = 1 ->
  n mod 2 = 1.
Proof.
  intro H.
  destruct (mod2_0_1 n) as [E|E]; auto 1.
  pose proof (ctzS_even_0 _ E) as H0.
  rewrite H0 in H.
  cbn in H.
  congruence.
Qed.

Lemma ctzS_even_mod4ne1 n:
  ctzS n mod 2 = 0 ->
  n mod 4 <> 1.
Proof.
  intros H H0.
  pose proof (ctzS_mod4eq1 _ H0) as H1.
  rewrite H1 in H.
  cbn in H.
  congruence.
Qed.

Lemma ctzS_mod2eq0_5 n:
  ctzS n mod 2 = 0 ->
  ctzS (1+n) mod 2 = 0 ->
  ctzS (2+n) mod 2 = 0 ->
  ctzS (3+n) mod 2 = 0 ->
  ctzS (4+n) mod 2 = 0 ->
  False.
Proof.
  intros.
  pose proof (ctzS_even_mod4ne1 _ H) as E.
  pose proof (ctzS_even_mod4ne1 _ H0) as E0.
  pose proof (ctzS_even_mod4ne1 _ H1) as E1.
  pose proof (ctzS_even_mod4ne1 _ H2) as E2.
  pose proof (ctzS_even_mod4ne1 _ H3) as E3.
  rewrite <-Div0.add_mod_idemp_r in E0,E1,E2,E3.
  remember (n mod 4) as v1.
  epose proof (mod_upper_bound n 4 _).
  Unshelve. 2: congruence.
  assert (v1=0\/v1=1\/v1=2\/v1=3) as X by lia.
  clear Heqv1.
  destruct X as [X|[X|[X|X]]]; subst v1; cbn in E0,E1,E2,E3; congruence.
Qed.

Lemma ctzS_chain_spec0 n0:
  forall n,
  n<n0 ->
  ctzS n mod 2 = 1 ->
  ctzS_chain (S n).
Proof.
  induction n0.
  1: intro; lia.
  intros n H H0.
  pose proof (ctzS_odd_odd _ H0) as H1.
  destruct n as [|n].
  1: cbn in H1; congruence.
  destruct n as [|n].
  { change 2 with (0+2).
    eapply ctzS_chain_S2; auto 1.
    constructor. }
  rewrite mod2_SS in H1.
  destruct (mod2_0_1 (ctzS n)) as [E|E].
  - destruct n as [|n].
    1: cbn in H1; congruence.
    destruct n as [|n].
    { change 4 with (0+4).
      eapply ctzS_chain_S4; auto 1.
      constructor. }
    replace (S(S(S(S(S n))))) with (S n+4) by lia.
    assert (ctzS (S n) mod 2 = 0) as E1. {
      rewrite ctzS_even_0.
      1: reflexivity.
      rewrite <-mod2_1_S.
      rewrite mod2_SS in H1.
      apply H1.
    }
    assert (ctzS (S (S (S n))) mod 2 = 0) as E3. {
      rewrite ctzS_even_0.
      1: reflexivity.
      cbn[add].
      rewrite mod2_SS.
      rewrite mod2_SS in H1.
      rewrite <-mod2_1_S.
      apply H1.
    }
    eapply ctzS_chain_S4.
    + apply IHn0.
      1: lia.
      destruct (mod2_0_1 (ctzS n)) as [E0|E0].
      2: apply E0.
      destruct n as [|n].
      1: cbn in H1; congruence.
      assert (ctzS n mod 2 = 0) as E'. {
        rewrite ctzS_even_0.
        1: reflexivity.
        rewrite mod2_SS,<-mod2_0_S in H1.
        apply H1.
      }
      destruct (ctzS_mod2eq0_5 _ E' E0 E1 E E3).
    + apply E1.
    + rewrite add_comm. apply E.
    + rewrite add_comm. apply E3.
    + rewrite add_comm. apply H0.
  - epose proof (IHn0 _ _ E).
    Unshelve. 2: lia.
    replace (S (S (S n))) with ((S n)+2) by lia.
    eapply ctzS_chain_S2; eauto 1.
    + rewrite ctzS_even_0.
      1: reflexivity.
      rewrite <-mod2_1_S.
      apply H1.
    + rewrite add_comm. apply H0.
Qed.

Lemma ctzS_chain_spec n:
  ctzS n mod 2 = 1 ->
  ctzS_chain (S n).
Proof.
  apply ctzS_chain_spec0 with (n0:=S n).
  lia.
Qed.

Inductive N'steps: (nat*(list nat))->nat->nat->(nat*(list nat))->nat->nat->Prop :=
| N'steps_O i e ne h1 h2:
  embanked_batch i e ne h1 h2 ->
  N'steps ne h1 h2 ne h1 h2
| N'steps_S i e ne nne h1 h2 h1a h2a h1b h2b:
  N'steps e h1 h2 ne h1a h2a ->
  embanked_batch i ne nne h1b h2b ->
  N'steps e h1 h2 nne h1b h2b
.



Hypothesis Sk:nat*(list nat).
Hypothesis Base_Sk: Base Sk.

Lemma embanked_batches_0 m0:
  m0 < 2^(k*2)-1 ->
  forall m,
  m<=m0 ->
  ctzS_chain m ->
  exists e ne,
  N'steps e (2^(k*2)-1) (2^(k*2)) ne (2^(k*2)-1-m) (2^(k*2)+m) /\
  embanked_batch (k*2+1) Sk e (2^(k*2)-1) (2^(k*2)) /\
  Add2s (k*2+1) Sk e /\
  (exists e' i', embanked_batch i' e' ne (2^(k*2)-1-m) (2^(k*2)+m) /\ i' mod 2 = 1) /\
  to_l ne = k*2+1 /\
  ai' 0 ne = 1+m*2 /\
  ai' 1 ne = 2^(k*2)+2+m*2 /\
  (forall i, ai i ne = ai i e + 2*(m/2^i)).
Proof.
  induction m0.
  - intros Hm0 m Hm Hcc.
    assert (m=0) by lia. subst.
    destruct (Base_embanked_batch Base_Sk) as [ne [Heb [Hl [Ha0 [Ha1 Ha]]]]].
    exists ne ne.
    rsplit; auto 1.
    + rewrite sub_0_r,add_0_r; eapply N'steps_O,Heb.
    + do 2 eexists.
      split. 1: rewrite sub_0_r,add_0_r; apply Heb.
      rewrite add_comm,Div0.mod_add.
      reflexivity.
    + lia.
    + intro i.
      rewrite Div0.div_0_l.
      lia.
  - intros Hm0 m Hm Hcc.
    inversion Hcc; subst.
    1: eapply IHm0; auto 1; lia.
    + eassert (_) as X. {
        apply IHm0.
        3: apply H.
        1,2: lia.
      }
      destruct X as [e [ne [HN [Heb0 [Hadd2s0 [Heb' [Hl [Ha0 [Ha1 Ha]]]]]]]]].
      destruct Heb' as [e' [i' [Heb' Hi']]].
      eassert (_) as X0. {
        eapply embanked_4batch with (m:=n).
        1: lia.
        3: apply Heb'.
        all: auto 1.
      }
      destruct X0 as [e2 [i2 [Heb2 [e3 [i3 [Heb3 [e4 [i4 [Heb4 [e5 [i5 [Heb5 [Hi5 [Hl5 [Ha50 [Ha51 Ha5]]]]]]]]]]]]]]]].
      exists e e5.
      rsplit.
      * eapply N'steps_S. 2: apply Heb5.
        eapply N'steps_S. 2: apply Heb4.
        eapply N'steps_S. 2: apply Heb3.
        eapply N'steps_S. 2: apply Heb2.
        apply HN.
      * auto 1.
      * auto 1.
      * exists e4 i5. tauto.
      * auto 1.
      * auto 1.
      * auto 1.
      * intro i.
        specialize (Ha i).
        specialize (Ha5 i).
        lia.
    + eassert (_) as X. {
        apply IHm0.
        3: apply H.
        1,2: lia.
      }
      destruct X as [e [ne [HN [Heb0 [Hadd2s0 [Heb' [Hl [Ha0 [Ha1 Ha]]]]]]]]].
      destruct Heb' as [e' [i' [Heb' Hi']]].
      eassert (_) as X0. {
        eapply embanked_8batch with (m:=n).
        1: lia.
        5: apply Heb'.
        all: auto 1.
      }
      destruct X0 as
        [e2 [i2 [Heb2 [e3 [i3 [Heb3 [e4 [i4 [Heb4 [e5 [i5 [Heb5
        [e6 [i6 [Heb6 [e7 [i7 [Heb7 [e8 [i8 [Heb8 [e9 [i9 [Heb9
        [Hi9 [Hl9 [Ha90 [Ha91 Ha9]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      exists e e9.
      rsplit.
      * eapply N'steps_S. 2: apply Heb9.
        eapply N'steps_S. 2: apply Heb8.
        eapply N'steps_S. 2: apply Heb7.
        eapply N'steps_S. 2: apply Heb6.
        eapply N'steps_S. 2: apply Heb5.
        eapply N'steps_S. 2: apply Heb4.
        eapply N'steps_S. 2: apply Heb3.
        eapply N'steps_S. 2: apply Heb2.
        apply HN.
      * auto 1.
      * auto 1.
      * exists e8 i9. tauto.
      * auto 1.
      * auto 1.
      * auto 1.
      * intro i.
        specialize (Ha i).
        specialize (Ha9 i).
        lia.
Qed.


(* m=2^(k*2)-2 is Corollary 4.2 *)
Lemma embanked_batches m:
  m < 2^(k*2)-1 ->
  ctzS_chain m ->
  exists e ne,
  N'steps e (2^(k*2)-1) (2^(k*2)) ne (2^(k*2)-1-m) (2^(k*2)+m) /\
  embanked_batch (k*2+1) Sk e (2^(k*2)-1) (2^(k*2)) /\
  Add2s (k*2+1) Sk e /\
  (exists e' i', embanked_batch i' e' ne (2^(k*2)-1-m) (2^(k*2)+m) /\ i' mod 2 = 1) /\
  to_l ne = k*2+1 /\
  ai' 0 ne = 1+m*2 /\
  ai' 1 ne = 2^(k*2)+2+m*2 /\
  (forall i, ai i ne = ai i e + 2*(m/2^i)). (* Proposition 4.3 *)
Proof.
  intros.
  apply embanked_batches_0 with (m0:=m); auto 1.
Qed.

Lemma pow22k_lower_bound: 2^(k*2)>=4.
Proof.
  destruct k as [|k']. 1: lia.
  cbn.
  pose proof (pow2_nez (k'*2)).
  lia.
Qed.

(* Corollary 4.2 *)
Lemma Sk_to_E':
  exists e ne,
  N'steps e (2^(k*2)-1) (2^(k*2)) ne 1 (2^(k*2)*2-2) /\
  embanked_batch (k*2+1) Sk e (2^(k*2)-1) (2^(k*2)) /\
  Add2s (k*2+1) Sk e /\
  (exists e' i', embanked_batch i' e' ne 1 (2^(k*2)*2-2) /\ i' mod 2 = 1) /\
  to_l ne = k*2+1 /\
  ai' 0 ne = 2^(k*2)*2-3 /\
  ai' 1 ne = 2^(k*2)*3-2 /\
  (forall i, ai i ne = ai i e + 2*((2^(k*2)-2)/2^i)).
Proof.
  pose proof pow22k_lower_bound as p22k_lb.
  eassert (_) as X. {
    apply (embanked_batches (2^(k*2)-2)).
    1: lia.
    replace (2^(k*2)-2) with (S(2^(k*2)-1-2)) by lia.
    apply ctzS_chain_spec.
    rewrite ctzS_sub. 2,3: lia.
    reflexivity.
  }
  destruct X as [e [ne [HN [Heb0 [Hadd2s0 [Heb' [Hl [Ha0 [Ha1 Ha]]]]]]]]].
  exists e ne.
  rsplit; auto 1.
  - applys_eq HN; lia.
  - destruct Heb' as [e' [i' [Heb' Hi']]].
    exists e' i'.
    split; auto 1.
    applys_eq Heb'; lia.
  - applys_eq Ha0; lia.
  - applys_eq Ha1; lia.
Qed.

Lemma pow2sub_div_pow2 i j c:
  j<=i ->
  0<c ->
  c<=2^j ->
  (2^i-c)/2^j = 2^(i-j) - 1.
Proof.
  intros Hj Hc1 Hc2.
  replace (2^i) with (2^(i-j+j)) by (f_equal; lia).
  rewrite pow_add_r.
  pose proof (pow2_nez (i-j)).
  replace (2^(i-j)) with ((2^(i-j)-1+1)) by lia.
  rewrite mul_add_distr_r,mul_1_l,<-add_sub_assoc; auto 1.
  rewrite div_add_l. 2: apply pow2_nez.
  rewrite div_small; lia.
Qed.

Lemma pow2sub2_div_pow2 i j:
  j<=i ->
  1<=j ->
  (2^i-2)/2^j = 2^(i-j) - 1.
Proof.
  intros.
  apply pow2sub_div_pow2; try lia.
  change (2<=2^j) with (2^1<=2^j).
  apply pow_le_mono_r; lia.
Qed.


Lemma Sk_to_E'':
  exists e ne,
  N'steps e (2^(k*2)-1) (2^(k*2)) ne 1 (2^(k*2)*2-2) /\
  embanked_batch (k*2+1) Sk e (2^(k*2)-1) (2^(k*2)) /\
  Add2s (k*2+1) Sk e /\
  (forall i, ai i ne = ai i e + 2*((2^(k*2)-2)/2^i)) /\
  exists n'ne,
  embanked_batch 1 ne n'ne 1 (2^(k*2)*2-1) /\
  to_l n'ne = k*2+1 /\
  ai' 0 n'ne = 2^(k*2)*2-3 /\
  ai' 1 n'ne = 2^(k*2)*3 /\
  (forall i, 2<=i -> i<=k*2 -> ai' i n'ne = 2^(k*2+1-i)*3-(1-(i mod 2))*2) /\
  ai' (k*2+1) n'ne = 2
.
Proof.
  pose proof pow22k_lower_bound as p22k_lb.
  destruct Sk_to_E' as [e [ne [HN [Heb0 [Hadd2s0 [[e' [i' [Heb' Hi']]] [Hl [Ha0 [Ha1 Ha]]]]]]]]].
  epose proof (embanked_batch_precond'' Heb' Hl _ _) as H.
  Unshelve. 2,3: lia.
  rewrite Hi' in H.
  destruct H as [n'ne Heb].
  change (2^(k*2)*2) with (2^(k*2)*2^1) in Heb.
  rewrite <-pow_add_r in Heb.
  replace (2^(k*2+1)-2) with (2^(k*2+1)-0-2) in Heb. 2: lia.
  rewrite ctzS_sub in Heb. 2: lia. 2: rewrite pow_add_r; cbn; lia.
  rewrite pow_add_r,sub_0_r in Heb.
  cbn in Heb.
  replace (2^(k*2)*2-2+1) with (2^(k*2)*2-1) in Heb by lia.
  pose proof (embanked_batch_Add2s Heb) as Ha'.
  destruct (embanked_batch_a0_a1 Heb) as [Ha0' Ha1'].
  cbn in Ha0',Ha1',Ha0,Ha1.
  rewrite Ha0 in Ha0'.
  rewrite Ha1 in Ha1'.
  exists e ne.
  rsplit; auto 1.
    exists n'ne. rsplit; auto 1.
    + epose proof (embanked_batch_len Heb).
      congruence.
    + cbn. lia.
    + cbn. lia.
    + intros i Hige Hile.
      destruct i as [|i]. 1: lia.
      unfold ai'.
      specialize (Ha i).
      inverts Ha'.
      specialize (Hadd2s (S i)). unfold ai' in Hadd2s.
      destruct (Nat.leb_spec (S i) 1) as [E|E]. 1: lia.
      cbn in Hadd2s. rewrite add_0_r in Hadd2s.
      gsubst (ai i n'ne) Hadd2s.
      rewrite Ha.
      inverts Base_Sk.
      specialize (Base_a i).
      destruct (Nat.ltb_spec i (k*2)) as [E3|E3]. 2: lia.
      inverts Hadd2s0.
      specialize (Hadd2s (S i)). unfold ai' in Hadd2s.
      destruct (Nat.leb_spec (S i) (k*2+1)) as [E0|E0]. 2: lia.
      destruct (even (k*2+1)) eqn:E1.
      1: {
        rewrite even_true_mod2 in E1.
        rewrite add_comm,Div0.mod_add in E1.
        cbn in E1; congruence.
      }
      pose proof (pow2_nez (k*2-i)) as E2'.
      destruct (even (S i)) eqn:E2.
      1: rewrite even_true_mod2 in E2.
      2: rewrite even_false_mod2 in E2.
      1,2: rewrite E2;
        cbn in Hadd2s; cbn;
        rewrite <-Hadd2s,Base_a;
        rewrite pow2sub2_div_pow2; try lia;
        replace (k*2+1-S i) with (k*2-i) by lia;
        lia.
    + rewrite add_comm. cbn.
      specialize (Ha (k*2)).
      inverts Ha'.
      specialize (Hadd2s (S (k*2))). unfold ai' in Hadd2s.
      destruct (Nat.leb_spec (S (k*2)) 1) as [E|E]. 1: lia.
      cbn in Hadd2s. rewrite add_0_r in Hadd2s.
      gsubst (ai (k*2) n'ne) Hadd2s.
      rewrite Ha.
      inverts Base_Sk.
      specialize (Base_a (k*2)).
      destruct (Nat.ltb_spec (k*2) (k*2)) as [E3|E3]. 1: lia.
      inverts Hadd2s0.
      specialize (Hadd2s (S (k*2))). unfold ai' in Hadd2s.
      destruct (Nat.leb_spec (S (k*2)) (k*2+1)) as [E0|E0]. 2: lia.
      replace (k*2+1) with (S(k*2)) in Hadd2s by lia.
      destruct (even (S(k*2))) eqn:E1.
      1: {
        rewrite even_true_mod2 in E1.
        rewrite <-add_1_l,add_comm in E1.
        rewrite add_comm,Div0.mod_add in E1.
        cbn in E1; congruence.
      }
      cbn in Hadd2s.
      rewrite <-Hadd2s,Base_a.
      rewrite pow2sub2_div_pow2; try lia.
      rewrite sub_diag. reflexivity.
Qed.


Lemma mod2_S x:
  (1-(x mod 2)) = (S x) mod 2.
Proof.
destruct (mod2_0_1 x) as [E|E].
- rewrite E.
  rewrite mod2_0_S in E.
  rewrite E.
  reflexivity.
- rewrite E.
  rewrite mod2_1_S in E.
  rewrite E.
  reflexivity.
Qed.

Lemma ai_out_of_bound_0 i s1:
  to_l s1 <= i ->
  ai i s1 = O.
Proof.
  destruct s1 as [x xs].
  cbn.
  rewrite grey_to_binary_length,length_map.
  apply nth_overflow.
Qed.

Inductive ZIHIO: (nat*(list nat))->(nat*(list nat))->Prop :=
| ZIHIO_intro n_1 n_2 s1 s2 s3 s4 s5 s6
  (Z12':Zero s1 s2)
  (I23':Increments n_1 s2 s3)
  (H34':Halve s3 s4)
  (I45':Increments (S n_2) s4 s5)
  (O56':Overflow s5 s6)
  (Hwf6':WF1 s6)
  (Hs6':to_s s6 = false)
  (Hn6':to_n s6 = 0)
  (Hl6':to_l s6 = k * 2 + 3)
  (Ha60':fst s6 = 1)
  (Ha61':ai 0 s6 = 2 ^ (k * 2 + 2) - 4)
  (Ha6':forall i : nat, 2 <= i -> i <= k * 2 + 2 -> ai' i s6 = 2 ^ (k * 2 + 3 - i) - i mod 2 * 2)
  (Ha6_last:ai' (k*2+3) s6 = 0):
  ZIHIO s1 s6.
  

Lemma E''_Overflow s1:
  (exists s0, embanked_batch 1 s0 s1 1 (2^(k*2)*2-1)) ->
  to_l s1 = k*2+1 ->
  ai' 0 s1 = 2^(k*2)*2-3 ->
  ai' 1 s1 = 2^(k*2)*3 ->
  (forall i, 2<=i -> i<=k*2 -> ai' i s1 = 2^(k*2+1-i)*3-(1-(i mod 2))*2) ->
  ai' (k*2+1) s1 = 2 ->
  exists s6, ZIHIO s1 s6.
Proof.
  pose proof pow22k_lower_bound as p22k_lb.

  intros Heb Hl1' Ha10 Ha11 Ha1 Ha1'.
  destruct Heb as [s0 Heb].
  destruct (embanked_batch_postcond Heb) as [Hwf1 [Hs1 [Hn1 [Hl1 Ha10_odd]]]].
  cbn in Ha10,Ha11.

  destruct (Zero_precond Hwf1 Hs1 Hn1) as [s2 [Z12 Hwf2]].

  pose proof (Zero_sgn Z12) as Hs2.
  pose proof (Zero_n Z12) as Hn2.
  pose proof (Zero_len Z12) as Hl2.
  pose proof (Zero_a0 Z12) as Ha20.
  pose proof (Zero_a1 Z12 Hl1) as Ha21.
  pose proof (Zero_a Z12) as Ha2.

  assert (Ha20_even:Even (fst s2)). {
    rewrite Ha20 in Ha10_odd.
    rewrite Odd_succ in Ha10_odd.
    apply Ha10_odd.
  }
  assert (Hn2_odd:Odd (to_n s2)). {
    rewrite Hn2.
    replace (to_l s1) with (1+(to_l s1 - 1)) by lia.
    rewrite pow2_1a.
    pose proof (pow2_nez (to_l s1 - 1)).
    destruct (2 ^ (to_l s1 - 1)). 1: congruence.
    replace (2*(S n)-1) with (S (2*n)) by lia.
    rewrite Odd_succ.
    econstructor; reflexivity.
  }
  eassert (I23:_). {
    apply (Increments_dec_precond2 (fst s2) Hwf2 Hs2).
    2: lia.
    rewrite <-Ha20.
    rewrite Hn2,Hl1',Ha10.
    rewrite pow_add_r; cbn.
    lia.
  }

  destruct I23 as [s3 [I23 Hwf3]].

  pose proof (Increments_sgn I23) as Hs3.
  pose proof (Increments_n I23) as Hn3.
  pose proof (Increments_len I23) as Hl3.
  pose proof (Increments_a0 I23) as Ha30.
  pose proof (Increments_a I23) as Ha3.
  rewrite Hs2 in Hn3,Ha30,Ha3.
  pose proof (Ha3 O) as Ha31.
  assert (Ha30_0:fst s3 = O) by lia.
  clear Ha30.
  pose proof (fun i => ai_out_of_bound_0 i s1) as Ha1o.
  gsubst_l (to_l s1) Hl1'.

  rewrite pow_add_r in Hn2; cbn in Hn2.
  assert (Ha21_expr:2^(k*2)*2-4 = fst s2) by lia.
  gsubst (fst s2) Ha21_expr.
  assert (Hn3_expr:3 = to_n s3) by lia.

  assert (Hn3gt1:to_n s3 > 1%nat) by lia.

  edestruct (Halve_precond2 Hwf3 Ha30_0) as [s4 [H34 Hwf4]]. 1: lia.
  pose proof (Halve_sgn H34) as Hs4.
  pose proof (Halve_n H34) as Hn4.
  pose proof (Halve_len H34) as Hl4.
  pose proof (Halve_a0 H34) as Ha40.
  pose proof (Halve_a H34) as Ha4.
  rewrite <-Hs3,Hs2 in Hs4.
  cbn in Hs4; symmetry in Hs4.
  gsubst (to_n s3) Hn3_expr.
  cbn in Hn4.
  assert (Hl4':to_l s4 = k*2+2) by lia.
  rewrite Hn2 in Ha31.
  change (2^(k*2)*2) with (2^(k*2)*2^1) in Ha31.
  rewrite <-pow_add_r in Ha31.
  rewrite divpow2r_pow2sub1 in Ha31. 2: lia.
  cbn in Ha31.
  rewrite add_sub in Ha31.
  gsubst_l (ai 0 s1) Ha11.
  gsubst (ai 0 s2) Ha21.
  assert (Ha31_expr:ai 0 s3 = 2^(k*2)*4-2) by lia.
  clear Ha31.

  eassert (I45:_). {
    apply (Increments_inc_precond2 (2^(k*2)*4-2) Hwf4 Hs4).
    3: lia.
    - rewrite Hl4',<-Hn4,add_sub. lia.
    - rewrite Hl4',<-Hn4.
      rewrite pow_add_r. cbn. lia.
  }
  destruct I45 as [s5 [I45 Hwf5]].
  pose proof (Increments_sgn I45) as Hs5.
  pose proof (Increments_n I45) as Hn5.
  pose proof (Increments_len I45) as Hl5.
  pose proof (Increments_a0 I45) as Ha50.
  pose proof (Increments_a I45) as Ha5.
  rewrite Hs4 in Hn5,Ha50,Ha5.
  assert (Ha50_expr:fst s5 = 1) by lia.
  clear Ha50.

  assert (Hn5_expr:to_n s5 = 2^(k*2)*4-1) by lia.
  clear Hn5.
  assert (Hl5_expr:to_l s5 = k*2+2) by lia.
  clear Hl5.
  assert (Hs5_expr:to_s s5 = true) by congruence.
  clear Hs5.

  eassert (O56:_). {
    apply (Overflow_precond Hwf5); auto 1.
    rewrite Hl5_expr.
    rewrite pow_add_r.
    cbn. auto 1.
  }
  destruct O56 as [s6 [O56 Hwf6]].
  pose proof (Overflow_sgn O56) as Hs6.
  pose proof (Overflow_n O56) as Hn6.
  pose proof (Overflow_len O56) as Hl6.
  pose proof (Overflow_a0 O56) as Ha60.
  pose proof (Overflow_a O56) as Ha6.
  assert (Ha60_expr:fst s6 = 1) by lia.
  clear Ha60.
  assert (Hl6_expr:to_l s6 = k*2+3) by lia.
  clear Hl6.

  gsubst (to_n s4) Hn4.
  gsubst_l (to_n s5) Hn5_expr.
  gsubst_l (to_n s2) Hn2.

  assert (Ha61_expr:ai 0 s6 = 2^(k*2+2)-4). {
    specialize (Ha6 O).
    gsubst (ai O s6) Ha6.
    gsubst_l (to_l s5) Hl5_expr.
    specialize (Ha5 O).
    specialize (Ha4 O).
    specialize (Ha3 (S O)).
    specialize (Ha2 (S O)).
    specialize (Ha1 (S (S O))).
    simpl_add_sub.
    simpl_add_sub_in Ha1.
    simpl_add_sub_in Ha2.
    change (2^(k*2)*2) with (2^(k*2)*2^1) in Ha3.
    change (2^(k*2)*4) with (2^(k*2)*2^2) in Ha5.
    rewrite <-pow_add_r in Ha3,Ha5.
    rewrite divpow2r_pow2sub1 in Ha3. 2: lia.
    rewrite divpow2r_pow2sub1 in Ha5. 2: lia.
    destruct (Nat.eqb_spec 0 (k*2+1)) as [E|E]. 1: lia. clear E.
    destruct (Nat.eqb_spec 1 (k*2)) as [E|E]. 1: lia. clear E.
    epose proof (Ha1 _ _) as Ha1_. clear Ha1.
    rename Ha1_ into Ha1.
    Unshelve. 2,3: lia.
    cbn in Ha1,Ha2,Ha3,Ha4,Ha5.
    simpl_add_sub_in Ha3.
    simpl_add_sub_in Ha5.
    replace (k*2+1) with (k*2-1+2) in Ha5 by lia.
    rewrite pow_add_r in Ha5.
    cbn in Ha5.
    replace (k*2+2) with (k*2-1+3) by lia.
    rewrite pow_add_r.
    cbn. lia.
  }
  assert (Ha6_last_expr:ai' (k*2+3) s6 = O). {
    replace (k*2+3) with (S(k*2+2)) by lia.
    unfold ai'.
    specialize (Ha6 (k*2+2)).
    gsubst (ai (k*2+2) s6) Ha6.
    gsubst_l (to_l s5) Hl5_expr.
    specialize (Ha5 (k*2+2)).
    specialize (Ha4 (k*2+2)).
    specialize (Ha3 (k*2+3)).
    specialize (Ha2 (k*2+3)).
    simpl_add_sub.
    simpl_add_sub_in Ha2.
    destruct (Nat.eqb_spec (k*2+2) (k*2+1)) as [E|E]. 1: lia. clear E.
    destruct (Nat.eqb_spec (k*2+3) (k*2)) as [E|E]. 1: lia. clear E.
    change (2^(k*2)*2) with (2^(k*2)*2^1) in Ha3.
    change (2^(k*2)*4) with (2^(k*2)*2^2) in Ha5.
    rewrite <-pow_add_r in Ha3,Ha5.
    rewrite divpow2r_pow2sub1_small in Ha3. 2: lia.
    rewrite divpow2r_pow2sub1_small in Ha5. 2: lia.
    change (3) with (2^2-1) in Ha3.
    change (1) with (2^1-1) in Ha5.
    rewrite divpow2r_pow2sub1_small in Ha3. 2: lia.
    rewrite divpow2r_pow2sub1_small in Ha5. 2: lia.
    cbn in Ha3,Ha5.
    replace (S(k*2+2)) with (k*2+3) in Ha4 by lia.
    rewrite Ha1o in Ha2; lia.
  }

  assert (Ha6_expr:forall i, 2<=i -> i<=k*2+2 -> ai' i s6 = 2^(k*2+3-i) - ((i mod 2))*2). {
    intros i Hi_ge Hi_le.
    destruct i as [|i]. 1: lia.
    unfold ai'.
    specialize (Ha6 i).
    gsubst (ai i s6) Ha6.
    gsubst_l (to_l s5) Hl5_expr.
    specialize (Ha5 i).
    specialize (Ha4 i).
    specialize (Ha3 (S i)).
    specialize (Ha2 (S i)).
    specialize (Ha1 (S (S i))).
    simpl_add_sub.
    simpl_add_sub_in Ha1.
    simpl_add_sub_in Ha2.
    rewrite (divpow2r_small 3) in Ha3. 2: {
      destruct i as [|i]. 1: lia.
      do 2 rewrite pow2_1a.
      pose proof (pow2_nez i).
      lia.
    }
    rewrite (divpow2r_small 1) in Ha5. 2: {
      destruct i as [|i]. 1: lia.
      rewrite pow2_1a.
      pose proof (pow2_nez i).
      lia.
    }
    assert (i<=k*2-2\/i=k*2-1\/i=k*2\/i=k*2+1) as Ei by lia.
    destruct Ei as [Ei|[Ei|[Ei|Ei]]].
    - destruct (Nat.eqb_spec i (k*2+1)) as [E|E]. 1: lia. clear E.
      destruct (Nat.eqb_spec (S i) (k*2)) as [E|E]. 1: lia. clear E.
      epose proof (Ha1 _ _) as Ha1_. clear Ha1.
      rename Ha1_ into Ha1.
      Unshelve. 2,3: lia.
      rewrite mod2_SS in Ha1.
      unfold ai' in Ha1.
      simpl_add_sub_in Ha2.
      gsubst (ai (S i) s2) Ha2.
      gsubst (ai (S i) s3) Ha4.
      gsubst_l (ai (S i) s1) Ha1.
      simpl_add_sub_in Ha3.
      simpl_add_sub_in Ha5.
      rewrite Ha5. clear Ha5.
      rewrite <-Ha3. clear Ha3.
      change (2^(k*2)*2) with (2^(k*2)*2^1).
      change (2^(k*2)*4) with (2^(k*2)*2^2).
      do 2 rewrite <-pow_add_r.
      rewrite divpow2r_pow2sub1. 2: lia.
      rewrite divpow2r_pow2sub1. 2: lia.
      simpl_add_sub.
      replace (k*2+1-i) with (k*2-(S i)+2) by lia.
      replace (k*2+2-i) with (k*2-(S i)+3) by lia.
      do 2 rewrite pow_add_r.
      rewrite mod2_S.
      assert (X1:2^1<=2^(k*2-(S i))) by (apply pow_le_mono_r; lia).
      cbn in X1. cbn.
      destruct (snd (divmod i 1 0 0)); lia.
    - destruct (Nat.eqb_spec i (k*2+1)) as [E|E]. 1: lia. clear E.
      destruct (Nat.eqb_spec (S i) (k*2)) as [E|E]. 2: lia. clear E.
      subst i. clear Ha1.
      rewrite add_comm in Ha1'.
      cbn in Ha1'.
      lia_gsubst (S (k*2-1)) (k*2).
      gsubst (ai (k*2) s1) Ha1'.
      gsubst (ai (k*2) s2) Ha2.
      gsubst_l (ai (k*2-1) s4) Ha4.
      simpl_add_sub_in Ha3.
      simpl_add_sub_in Ha5.
      rewrite Ha5. clear Ha5.
      rewrite <-Ha3. clear Ha3.
      change (2^(k*2)*2) with (2^(k*2)*2^1).
      change (2^(k*2)*4) with (2^(k*2)*2^2).
      do 2 rewrite <-pow_add_r.
      rewrite divpow2r_pow2sub1. 2: lia.
      rewrite divpow2r_pow2sub1. 2: lia.
      simpl_add_sub.
      assert (Ev:Even (k*2)). {
        econstructor.
        apply mul_comm.
      }
      OE_oe.
      rewrite even_true_mod2 in Ev.
      rewrite Ev. cbn.
      replace (k*2+1-(k*2-1)) with 2 by lia.
      replace (k*2+2-(k*2-1)) with 3 by lia.
      reflexivity.
    - destruct (Nat.eqb_spec i (k*2+1)) as [E|E]. 1: lia. clear E.
      destruct (Nat.eqb_spec (S i) (k*2)) as [E|E]. 1: lia. clear E.
      subst i. clear Ha1 Ha1'.
      rewrite Ha1o in Ha2. 2: lia.
      gsubst (ai (S(k*2)) s2) Ha2.
      gsubst_l (ai (k*2) s4) Ha4.
      simpl_add_sub_in Ha3.
      simpl_add_sub_in Ha5.
      rewrite Ha5. clear Ha5.
      rewrite <-Ha3. clear Ha3.
      change (2^(k*2)*2) with (2^(k*2)*2^1).
      change (2^(k*2)*4) with (2^(k*2)*2^2).
      do 2 rewrite <-pow_add_r.
      rewrite divpow2r_pow2sub1_small. 2: lia.
      rewrite divpow2r_pow2sub1. 2: lia.
      simpl_add_sub.
      assert (Od:Odd (S(k*2))) by (exists k; lia).
      OE_oe.
      unfold odd in Od.
      rewrite Bool.negb_true_iff in Od.
      rewrite even_false_mod2 in Od.
      rewrite Od. cbn.
      reflexivity.
    - destruct (Nat.eqb_spec i (k*2+1)) as [E|E]. 2: lia. clear E.
      destruct (Nat.eqb_spec (S i) (k*2)) as [E|E]. 1: lia. clear E.
      subst i. clear Ha1 Ha1'.
      rewrite Ha1o in Ha2. 2: lia.
      gsubst (ai (S(k*2+1)) s2) Ha2.
      gsubst_l (ai (k*2+1) s4) Ha4.
      simpl_add_sub_in Ha3.
      simpl_add_sub_in Ha5.
      rewrite Ha5. clear Ha5.
      rewrite <-Ha3. clear Ha3.
      change (2^(k*2)*2) with (2^(k*2)*2^1).
      change (2^(k*2)*4) with (2^(k*2)*2^2).
      do 2 rewrite <-pow_add_r.
      rewrite divpow2r_pow2sub1_small. 2: lia.
      rewrite divpow2r_pow2sub1. 2: lia.
      simpl_add_sub.
      assert (Ev:Even (S(k*2+1))) by (exists (S k); lia).
      OE_oe.
      rewrite even_true_mod2 in Ev.
      rewrite Ev. cbn.
      reflexivity.
  }
  replace (2^(k*2)*4-2) with (S(2^(k*2)*4-3)) in I45 by lia.
  exists s6.
  econstructor; eauto 1.
Qed.

Lemma ZIHIO_emb e ne:
  ZIHIO e ne ->
  exists ne',
  embanked ne ne' (2^(k*2+3)-1) (2^(k*2+2)-1) (2^(k*2+3)-4) (2^(k*2+2)-2).
Proof.
  intro HZ.
  inversion HZ; subst.
  eassert _ as Hwe. {
    apply (weakly_embanked_precond ne); auto 1.
    - lia.
    - rewrite Ha60'.
      exists 0. reflexivity.
    - rewrite Hl6',Ha60'.
      rewrite pow_add_r. cbn.
      pose proof (pow2_nez (k*2)).
      lia.
    - rewrite Hl6',Ha61'.
      simpl_add_sub.
      pose proof (pow2_nez (k*2+2)).
      lia.
  }
  destruct Hwe as [ne' [s_1 [s_2 [h_1 [h_2 Hwe]]]]].
  inversion Hwe; subst.
  gsubst_l (fst ne) Ha60'.
  gsubst_l (ai 0 ne) Ha61'.
  gsubst_l (to_l ne) Hl6'.
  cbn in n3_expr,n4_expr,n5_expr.
  simpl_add_sub_in n3_expr.
  simpl_add_sub_in n4_expr.
  simpl_add_sub_in n5_expr.
  simpl_add_sub_in n6_expr.
  simpl_add_sub_in a60_expr.
  epose proof (Ha6' 2 _ _) as Ha62.
  Unshelve. 2,3: lia.
  cbn in Ha62.
  simpl_add_sub_in Ha62.
  gsubst_l (ai 1ne) Ha62.
  assert (n3_expr':to_n s3' = 2^(k*2+3)-1) by lia. clear n3_expr.
  assert (n4_expr':to_n s4' = 2^(k*2+2)-1) by lia. clear n4_expr.
  rewrite n3_expr',n4_expr',n5_expr in a60_expr.
  rewrite divpow2r_pow2sub1 in a60_expr. 2: lia.
  rewrite divpow2r_pow2sub1 in a60_expr. 2: lia.
  rewrite divpow2r_0 in a60_expr.
  simpl_add_sub_in a60_expr.
  repeat rewrite pow_add_r in a60_expr.
  change (2^2) with 4 in a60_expr.
  replace (2^(k*2)*4-4+2^(k*2)*4+1) with ((2^(k*2)*4-2)*2+1) in a60_expr by lia.
  rewrite div_add_l in a60_expr. 2: lia.
  cbn in a60_expr.

  repeat rewrite pow_add_r in n6_expr.
  change (2^2) with 4 in n6_expr.
  replace ((2^(k*2)*4-4)) with ((2^(k*2)*2-2)*2) in n6_expr by lia.
  rewrite div_mul in n6_expr. 2: lia.
  cbn in n6_expr.
  pose proof (pow2_nez (k*2)) as Hp.

  eassert _ as He. {
    apply (embanked_precond Hwe).
    lia.
  }
  rewrite pow_add_r in n5_expr. cbn in n5_expr.
  assert (n5_expr':to_n s5' = 2^(k*2+3)-4) by (rewrite pow_add_r; cbn; lia). clear n5_expr.
  assert (n6_expr':to_n ne' = 2^(k*2+2)-2) by (rewrite pow_add_r; cbn; lia). clear n6_expr.
  rewrite n3_expr',n4_expr',n5_expr',n6_expr' in He.
  destruct He as [ne'0 He].

  eexists.
  apply He.
Qed.

Ltac simpl_divpow2r_pow2sub1 H :=
  repeat (
  (rewrite divpow2r_pow2sub1 in H; [idtac|lia;fail])||
  (rewrite divpow2r_pow2sub1_small in H; [idtac|lia;fail])).

Ltac simpl_a7_expr a7_expr :=
  simpl_divpow2r_pow2sub1 a7_expr;
  simpl_add_sub_in a7_expr;
  repeat rewrite pow_add_r in a7_expr;
  change (2^3) with 8 in a7_expr;
  change (2^2) with 4 in a7_expr;
  replace (2^(k*2)*4-2) with ((2^(k*2)*2-1)*2) in a7_expr by lia;
  replace (2^(k*2)*8-4) with ((2^(k*2)*2-1)*2*2) in a7_expr by lia;
  (repeat rewrite <-divpow2r_div2 in a7_expr);
  (repeat (rewrite div_mul in a7_expr; [idtac|congruence]));
  replace (2^(k*2)*2) with (2^(k*2+1)) in a7_expr by (rewrite pow_add_r; cbn; reflexivity);
  simpl_divpow2r_pow2sub1 a7_expr;
  simpl_add_sub_in a7_expr.


Lemma ZIHIO_emb_Add2 e ne ne':
  ZIHIO e ne ->
  embanked ne ne' (2^(k*2+3)-1) (2^(k*2+2)-1) (2^(k*2+3)-4) (2^(k*2+2)-2) ->
  Add2 (k*2+1) ne ne'.
Proof.
  intros HZ He.
  inversion HZ; subst.
  inversion He; subst.
  constructor.
  intro i.
  pose proof (fun i => ai_out_of_bound_0 i ne) as Hao.
  gsubst_l (to_l ne) Hl6'.
  simpl_add_sub_in a70_expr.
  pose proof (pow22k_lower_bound) as Hp.
  rewrite Hs7n in a70_expr.
  assert (i=0\/i=1\/(2<=i/\i<=k*2-1)\/(i=k*2)\/(i=k*2+1)\/(i=k*2+2)\/(i=k*2+3)\/k*2+4<=i) as E by lia.
  destruct E as [E|E].
  {
    subst i.
    rewrite (add_comm (k*2) 1).
    cbn.
    repeat rewrite divpow2r_0 in a70_expr.
    rewrite divpow2r_pow2sub1 in a70_expr. 2: lia.
    simpl_add_sub_in a70_expr.
    repeat rewrite pow_add_r in a70_expr.
    change (2^3) with 8 in a70_expr.
    change (2^2) with 4 in a70_expr.
    change (2^1) with 2 in a70_expr.
    destruct (Nat.eqb_spec 2 (k*2+2)) as [E0|E0]. 1: lia.
    remember (2^(k*2)) as v1.
    rewrite sub_add in a70_expr. 2: lia.
    replace (v1*8-4+1) with ((v1*4-2)*2+1) in a70_expr by lia.
    rewrite div_add_l in a70_expr. 2: lia.
    replace (v1*4/2) with (v1*2*2/2) in a70_expr by (f_equal; lia).
    rewrite div_mul in a70_expr. 2: lia.
    cbn in a70_expr.
    epose proof (Ha6' 2 _ _) as Ha6.
    Unshelve. 2,3: lia.
    cbn in Ha6.
    simpl_add_sub_in Ha6.
    rewrite Ha6 in a70_expr.
    rewrite pow_add_r in a70_expr.
    cbn in a70_expr.
    lia.
  }
  destruct i as [|i]. 1: lia.
  specialize (a7_expr i).
  simpl_add_sub_in a7_expr.
  clear a70_expr.
  destruct E as [E|E].
  {
    inverts E.
    destruct (Nat.eqb_spec 1 (k*2+1)) as [E'|E']. 1: lia. clear E'.
    destruct (Nat.eqb_spec 2 (k*2+2)) as [E'|E']. 1: lia. clear E'.

    simpl_divpow2r_pow2sub1 a7_expr.
    simpl_add_sub_in a7_expr.
    repeat rewrite pow_add_r in a7_expr.
    change (2^3) with 8 in a7_expr.
    change (2^2) with 4 in a7_expr.
    repeat rewrite <-divpow2r_div2 in a7_expr.
    replace (2^(k*2)*8-4) with ((2^(k*2)*4-2)*2) in a7_expr by lia.
    rewrite div_mul in a7_expr. 2: lia.
    rewrite divpow2r_0 in a7_expr.
    replace (2^(k*2)*4-2) with ((2^(k*2)*2-1)*2) in a7_expr by lia.
    rewrite div_add_l in a7_expr. 2: lia.
    cbn in a7_expr. cbn.
    rewrite Ha61'.
    rewrite pow_add_r; cbn.
    epose proof (Ha6' 3 _ _) as Ha6.
    Unshelve. 2,3: lia.
    cbn in Ha6.
    simpl_add_sub_in Ha6.
    rewrite Ha6 in a7_expr. clear Ha6.
    lia.
  }
  destruct E as [E|E].
  {
    destruct (Nat.eqb_spec (S i) (k*2+1)) as [E'|E']. 1: lia. clear E'.
    destruct (Nat.eqb_spec (S (S i)) (k*2+2)) as [E'|E']. 1: lia. clear E'.
    simpl_divpow2r_pow2sub1 a7_expr.
    simpl_add_sub_in a7_expr.

    epose proof (Ha6' (S(S(S i))) _ _) as Ha6.
    Unshelve. 2,3: lia.
    unfold ai' in Ha6. unfold ai'.
    simpl_add_sub_in Ha6.
    rewrite Ha6 in a7_expr. clear Ha6.

    epose proof (Ha6' (((S i))) _ _) as Ha6.
    Unshelve. 2,3: lia.
    unfold ai' in Ha6. unfold ai'.
    simpl_add_sub_in Ha6.
    rewrite Ha6. clear Ha6.

    repeat rewrite pow_add_r in a7_expr.
    change (2^3) with 8 in a7_expr.
    change (2^2) with 4 in a7_expr.
    replace (2^(k*2)*4-2) with ((2^(k*2)*2-1)*2) in a7_expr by lia.
    replace (2^(k*2)*8-4) with ((2^(k*2)*2-1)*2*2) in a7_expr by lia.
    destruct i as [|i]. 1: lia.
    repeat rewrite <-divpow2r_div2 in a7_expr.
    repeat (rewrite div_mul in a7_expr; [idtac|congruence]).
    replace (2^(k*2)*2) with (2^(k*2+1)) in a7_expr by (rewrite pow_add_r; cbn; reflexivity).
    rewrite divpow2r_pow2sub1 in a7_expr. 2: lia.
    simpl_add_sub_in a7_expr.
    repeat rewrite mod2_SS in a7_expr.
    replace (2^(k*2-i)) with (2^(1+(k*2-S i))) in a7_expr by (f_equal; lia).
    rewrite pow2_1a in a7_expr.
    rewrite mod2_SS.
    pose proof (mod_upper_bound i 2) as H.
    replace (k*2+2-S i) with (1+(1+(k*2-S i))) by lia.
    do 2 rewrite pow2_1a.
    assert (2^2<=2^(k*2-S i)) as H0 by (apply pow_le_mono_r; lia).
    cbn in H0.
    lia.
  }
  destruct E as [E|E].
  {
    destruct (Nat.eqb_spec (S i) (k*2+1)) as [E'|E']. 1: lia. clear E'.
    destruct (Nat.eqb_spec (S (S i)) (k*2+2)) as [E'|E']. 1: lia. clear E'.
    assert (i=S(k*2-2)) by lia. subst i.

    simpl_a7_expr a7_expr.

    replace (k*2-(k*2-2)) with 2 in a7_expr by lia.
    replace (k*2-S(k*2-2)) with 1 in a7_expr by lia.
    cbn in a7_expr. cbn.
    replace (S(S(S(k*2-2)))) with (k*2+1) in a7_expr by lia.

    epose proof (Ha6' (S(k*2+1)) _ _) as Ha6.
    Unshelve. 2,3: lia.
    unfold ai' in Ha6. unfold ai'.
    simpl_add_sub_in Ha6.
    rewrite Ha6 in a7_expr. clear Ha6.

    epose proof (Ha6' (S(S(k*2-2))) _ _) as Ha6.
    Unshelve. 2,3: lia.
    unfold ai' in Ha6. unfold ai'.
    simpl_add_sub_in Ha6.
    rewrite Ha6. clear Ha6.

    replace (k*2+1) with (S(k*2)) in a7_expr by lia.
    rewrite mod2_SS,Div0.mod_mul in a7_expr.
    cbn in a7_expr.

    replace (k*2+1-(k*2-2)) with 3 by lia.
    replace (S(S(k*2-2))) with (k*2) by lia.
    rewrite Div0.mod_mul.
    cbn. lia.
  }
  destruct E as [E|E].
  {
    destruct (Nat.eqb_spec (S i) (k*2+1)) as [E'|E']. 2: lia. clear E'.
    destruct (Nat.eqb_spec (S (S i)) (k*2+2)) as [E'|E']. 2: lia. clear E'.
    assert (i=S(k*2-1)) by lia. subst i.

    simpl_a7_expr a7_expr.

    replace (k*2-(k*2-1)) with 1 in a7_expr by lia.
    replace (k*2-S(k*2-1)) with 0 in a7_expr by lia.
    cbn in a7_expr. cbn.
    replace (S(S(S(k*2-1)))) with (k*2+2) in a7_expr by lia.

    replace (k*2+3) with (S(k*2+2)) in Ha6_last by lia.
    unfold ai' in Ha6_last.
    rewrite Ha6_last in a7_expr.

    epose proof (Ha6' (S(S(k*2-1))) _ _) as Ha6.
    Unshelve. 2,3: lia.
    unfold ai' in Ha6. unfold ai'.
    simpl_add_sub_in Ha6.
    rewrite Ha6. clear Ha6.

    cbn in a7_expr.

    replace (k*2+1-(k*2-1)) with 2 by lia.
    replace (S(S(k*2-1))) with (1+k*2) by lia.
    rewrite Div0.mod_add.
    cbn. lia.
  }
  destruct E as [E|E].
  {
    destruct (Nat.eqb_spec (S i) (k*2+1)) as [E'|E']. 1: lia. clear E'.
    destruct (Nat.eqb_spec (S (S i)) (k*2+2)) as [E'|E']. 1: lia. clear E'.
    assert (i=S(k*2)) by lia. subst i.

    simpl_a7_expr a7_expr.

    cbn in a7_expr. cbn.
    rewrite Hao in a7_expr. 2: lia.

    epose proof (Ha6' (S(S(k*2))) _ _) as Ha6.
    Unshelve. 2,3: lia.
    unfold ai' in Ha6. unfold ai'.
    simpl_add_sub_in Ha6.
    rewrite Ha6. clear Ha6.

    cbn in a7_expr.

    rewrite mod2_SS.
    rewrite Div0.mod_mul.
    cbn. lia.
  }
  destruct E as [E|E].
  {
    destruct (Nat.eqb_spec (S i) (k*2+1)) as [E'|E']. 1: lia. clear E'.
    destruct (Nat.eqb_spec (S (S i)) (k*2+2)) as [E'|E']. 1: lia. clear E'.
    assert (i=S(k*2+1)) by lia. subst i.

    simpl_a7_expr a7_expr.
    rewrite Hao in a7_expr. 2: lia.

    lia_gsubst (S(k*2+1)) (k*2+2).
    cbn.
    replace (k*2+3) with (S(k*2+2)) in Ha6_last by lia.
    cbn in Ha6_last.
    rewrite Ha6_last.
    lia.
  }
  {
    destruct (Nat.eqb_spec (S i) (k*2+1)) as [E'|E']. 1: lia. clear E'.
    destruct (Nat.eqb_spec (S (S i)) (k*2+2)) as [E'|E']. 1: lia. clear E'.
    cbn.
    rewrite Hao. 2: lia.
    rewrite ai_out_of_bound_0; lia.
  }
Qed.

Lemma ZIHIO_embanked_batch e ne ne':
  ZIHIO e ne ->
  embanked ne ne' (2^(k*2+3)-1) (2^(k*2+2)-1) (2^(k*2+3)-4) (2^(k*2+2)-2) ->
  exists n'ne,
  embanked_batch (k*2+1) ne n'ne (2^(k*2+2)-1) (2^(k*2+2)-2) /\
  to_l n'ne = k*2+3 /\
  ai' 0 n'ne = 1 /\
  ai' 1 n'ne = 2^(k*2+2)-2 /\
  (forall i, 2<=i -> ai' i n'ne = if i<? k*2+3 then 2^(k*2+3-i) else 0).
Proof.
  intros HZ He.
  epose proof (ZIHIO_emb_Add2 _ _ _ HZ He) as Ha.
  destruct (embanked__embanked_batch He Ha) as [n'ne Heb].

  eexists.
  split. 1: apply Heb.

  inversion HZ; subst.
  rewrite <-(embanked_batch_len Heb).
  split. 1: auto 1.

  destruct (embanked_batch_a0_a1 Heb) as [Ha0 Ha1].
  rewrite Ha0,Ha1. clear Ha0 Ha1.
  assert (E:(k*2+1) mod 2 = 1) by (rewrite add_comm,Div0.mod_add; reflexivity).
  rewrite E.
  assert (Hp':2^2<=2^(k*2+2)) by (apply pow_le_mono_r; lia).
  cbn in Hp'.
  rsplit.
  1,2: cbn; lia.
  intros i Hi.

  epose proof (embanked_batch_Add2s Heb) as HA.
  inverts HA.
  specialize (Hadd2s i).
  rewrite <-even_false_mod2 in E.
  rewrite E in Hadd2s.

  specialize (Ha6' i Hi).
  destruct (Nat.ltb_spec i (k*2+3)) as [E0|E0].
  - rewrite Ha6' in Hadd2s. 2: lia.
    destruct (even i) eqn:E2.
    + rewrite even_true_mod2 in E2.
      rewrite E2 in Hadd2s.
      rewrite Bool.andb_comm in Hadd2s.
      cbn in Hadd2s. lia.
    + rewrite even_false_mod2 in E2.
      rewrite E2 in Hadd2s.
      destruct (Nat.leb_spec i (k*2+1)) as [E3|E3].
      * cbn in Hadd2s.
        assert (Hp'':2^2<=2^(k*2+3-i)) by (apply pow_le_mono_r; lia).
        cbn in Hp''. lia.
      * assert (i=k*2+2) by lia. subst i.
        rewrite add_comm,Div0.mod_add in E2.
        cbn in E2.
        congruence.
  - destruct (Nat.leb_spec i (k*2+1)) as [E3|E3]. 1: lia.
    cbn in Hadd2s.
    assert (i=k*2+3\/i>=k*2+4) as [E4|E4] by lia.
    1: subst i; lia.
    rewrite <-Hadd2s.
    destruct i as [|i]. 1: lia.
    cbn.
    rewrite ai_out_of_bound_0; lia.
Qed.

End Sk.

Lemma last_step k e ne:
  embanked_batch (k*2+1) e ne (2^(k*2+2)-1) (2^(k*2+2)-2) ->
  to_l ne = k*2+3 ->
  ai' 0 ne = 1 ->
  ai' 1 ne = 2^(k*2+2)-2 ->
  (forall i, 2<=i -> ai' i ne = if i<? k*2+3 then 2^(k*2+3-i) else 0) ->
  exists b h_1 h_2,
  embanked_batch 1 ne b h_1 h_2 /\
  Base (k+1) b.
Proof.
  intros Heb Hl Ha0 Ha1 Ha.
  cbn in Ha0,Ha1.
  eassert _ as Heb'. {
    apply (embanked_batch_precond' Heb).
    - rewrite Hl.
      rewrite pow_add_r; cbn.
      pose proof (pow2_nez (k*2)). lia.
    - gen Ha1.
      rewrite Hl.
      simpl_add_sub.
      rewrite pow_add_r; cbn.
      pose proof (pow2_nez (k*2)). lia.
  }
  rewrite add_comm,Div0.mod_add in Heb'.
  cbn in Heb'.
  replace (2^(k*2+2)-2) with (2^(k*2+2)-0-2) in Heb' by lia.

  erewrite ctzS_sub in Heb'. 2: lia.
  2: rewrite pow_add_r; cbn; pose proof (pow2_nez (k*2)); lia.

  simpl_add_sub_in Heb'.
  cbn in Heb'.
  destruct Heb' as [b Heb'].

  epose proof (embanked_batch_Add2s Heb') as HA.
  inverts HA.
  do 3 eexists.
  split. 1: apply Heb'.

  constructor.
  - specialize (Hadd2s 0).
    cbn in Hadd2s. lia.
  - intro i.
    specialize (Hadd2s (S i)).
    destruct i as [|i].
    + cbn in Hadd2s.
      destruct (Nat.ltb_spec 0 ((k+1)*2)) as [E|E]. 2: lia.
      rewrite mul_add_distr_r. cbn.
      simpl_add_sub.
      assert (2^2<=2^(k*2+2)) as E0 by (apply pow_le_mono_r; lia).
      cbn in E0.
      lia.
    + assert (2<=S(S i)) as E1 by lia.
      specialize (Ha _ E1).
      lia_gsubst ((k+1)*2) (k*2+2).
      simpl_add_sub_in Ha.
      simpl_add_sub.
      cbn in Hadd2s.
      destruct (Nat.ltb_spec (S i) (k*2+2)) as [E2|E2];
        destruct (Nat.ltb_spec (S (S i)) (k*2+3)) as [E3|E3]; cbn in Ha; lia.
  - epose proof (embanked_batch_len Heb').
    lia.
Qed.

Lemma Increment_precond_toConfig {s1 s2}:
  Increment s1 s2 ->
  exists c1, toConfig s1 c1.
Proof.
  intro I.
  inversion I; subst.
  - eexists. constructor.
  - eexists. constructor.
Qed.

Lemma Increments_precond_toConfig {n s1 s2}:
  Increments (S n) s1 s2 ->
  exists c1, toConfig s1 c1.
Proof.
  intro I.
  inverts I.
  apply (Increment_precond_toConfig H0).
Qed.

Lemma Zero_precond_toConfig {s1 s2}:
  Zero s1 s2 ->
  exists c1, toConfig s1 c1.
Proof.
  intro I.
  inverts I.
  eexists. constructor.
Qed.

Lemma Overflow_precond_toConfig {s1 s2}:
  Overflow s1 s2 ->
  exists c1, toConfig s1 c1.
Proof.
  intro I.
  inverts I.
  eexists. constructor.
Qed.


Lemma toConfig_TryHalve_id {s1 c1}:
  toConfig s1 c1 ->
  TryHalve s1 s1.
Proof.
  intro H.
  inverts H.
  constructor.
Qed.

Lemma Increments_toConfig {n s1 s2 s3 c1 c3}:
  Increments (S n) s1 s2 ->
  TryHalve s2 s3 ->
  toConfig s1 c1 ->
  toConfig s3 c3 ->
  c1 -->* c3.
Proof.
  gen s1 s2 s3 c1 c3.
  induction n.
  - introv I12 H23 C1 C3.
    inverts I12.
    inverts H1.
    eapply Increment_toConfig; eauto 1.
  - introv I12 H23 C1 C3.
    inverts I12.
    destruct (Increments_precond_toConfig H1) as [c6 C6].
    pose proof (toConfig_TryHalve_id C6) as TH.
    follow (Increment_toConfig _ _ _ _ _ H0 TH C1 C6).
    eapply IHn; eauto 1.
Qed.

Lemma Halve_TryHalve{s1 s2}:
  Halve s1 s2 ->
  TryHalve s1 s2.
Proof.
  intro H.
  inverts H.
  constructor.
Qed.

Lemma ZIH_toConfig {n s1 s2 s3 s4 c1 c4}:
  Zero s1 s2 ->
  Increments n s2 s3 ->
  Halve s3 s4 ->
  toConfig s1 c1 ->
  toConfig s4 c4 ->
  c1 -->* c4.
Proof.
  intros Z12 I23 H34 C1 C4.
  destruct n as [|n].
  - inverts I23.
    inverts H34.
    eapply Zero_toConfig; eauto 1.
    constructor.
  - destruct (Increments_precond_toConfig I23) as [c5 C5].
    pose proof (toConfig_TryHalve_id C5) as TH.
    follow (Zero_toConfig _ _ _ _ _ Z12 TH C1 C5).
    eapply Increments_toConfig; eauto 2 using Halve_TryHalve.
Qed.

Lemma embanked_toConfig {s1 s7 c1 c7 s_1 h_1 s_2 h_2}:
  embanked s1 s7 s_1 h_1 s_2 h_2 ->
  toConfig s1 c1 ->
  toConfig s7 c7 ->
  c1 -->* c7.
Proof.
  intros He C1 C7.
  inversion He; subst.
  inversion Hwemb; subst.
  destruct (Increments_precond_toConfig I45') as [c4 C4].
  pose proof (toConfig_TryHalve_id C4) as TH.
  follow (ZIH_toConfig Z12' I23' H34' C1 C4).
  pose proof (Halve_TryHalve H56') as TH'.
  destruct n1' as [|n1'].
  - inverts I67.
    apply (Increments_toConfig I45' TH' C4 C7).
  - destruct (Increments_precond_toConfig I67) as [c6 C6].
    follow (Increments_toConfig I45' TH' C4 C6).
    pose proof (toConfig_TryHalve_id C7) as TH''.
    apply (Increments_toConfig I67 TH'' C6 C7).
Qed.

Lemma embanked_precond_toConfig {e ne s_1 h_1 s_2 h_2}:
  embanked e ne s_1 h_1 s_2 h_2 ->
  exists c, toConfig e c.
Proof.
  intro He.
  inverts He.
  inverts Hwemb.
  eapply Zero_precond_toConfig; eauto 1.
Qed.

Lemma embanked_postcond_toConfig {e ne s_1 h_1 s_2 h_2}:
  embanked e ne s_1 h_1 s_2 h_2 ->
  exists c, toConfig ne c.
Proof.
  intro He.
  inverts He.
  eapply Zero_precond_toConfig; eauto 1.
Qed.

Lemma embanked_batch_precond_toConfig {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  exists c, toConfig e c.
Proof.
  intro Heb.
  inverts Heb;
    eapply embanked_precond_toConfig; eauto 1.
Qed.

Lemma embanked_batch_postcond_toConfig {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  exists c, toConfig ne c.
Proof.
  intro Heb.
  induction Heb.
  - eapply embanked_postcond_toConfig; eauto 1.
  - eapply embanked_postcond_toConfig; eauto 1.
  - eapply IHHeb.
Qed.

Lemma embanked_batch_toConfig {i e ne h_1 h_2 c1 c2}:
  embanked_batch i e ne h_1 h_2 ->
  toConfig e c1 ->
  toConfig ne c2 ->  
  c1 -->* c2.
Proof.
  intros Heb.
  gen c1 c2.
  induction Heb; introv C1 C2.
  1,2: eapply embanked_toConfig; eauto 1.
  destruct (embanked_batch_precond_toConfig Heb) as [c3 C3].
  follow (embanked_toConfig He C1 C3).
  eapply IHHeb; eauto 1.
Qed.

Lemma N'steps_precond_toConfig{e h1a h2a ne h1b h2b}:
  N'steps e h1a h2a ne h1b h2b ->
  exists c, toConfig e c.
Proof.
  intro HN.
  induction HN.
  - eapply embanked_batch_postcond_toConfig; eauto 1.
  - eapply IHHN.
Qed.

Lemma N'steps_postcond_toConfig{e h1a h2a ne h1b h2b}:
  N'steps e h1a h2a ne h1b h2b ->
  exists c, toConfig ne c.
Proof.
  intro HN.
  destruct HN;
    eapply embanked_batch_postcond_toConfig; eauto 1.
Qed.

Lemma N'steps_toConfig{e h1a h2a ne h1b h2b c1 c2}:
  N'steps e h1a h2a ne h1b h2b ->
  toConfig e c1 ->
  toConfig ne c2 ->  
  c1 -->* c2.
Proof.
  intro HN.
  gen c1 c2.
  induction HN; introv C1 C2.
  - inverts C1. inverts C2.
    finish.
  - destruct (embanked_batch_precond_toConfig H) as [c3 C3].
    follow IHHN.
    eapply embanked_batch_toConfig; eauto 1.
Qed.

Lemma OZIH_toConfig {n s1 s2 s3 s4 s5 c1 c5}:
  Overflow s1 s2 ->
  Zero s2 s3 ->
  Increments n s3 s4 ->
  Halve s4 s5 ->
  toConfig s1 c1 ->
  toConfig s5 c5 ->
  c1 -->* c5.
Proof.
  intros O12 Z23 I34 H45 C1 C5.
  pose proof (Halve_TryHalve H45) as TH45.
  destruct n as [|n].
  - inverts I34.
    eapply (Overflow_toConfig); eauto 1.
  - destruct (Increments_precond_toConfig I34) as [c3 C3].
    epose proof (toConfig_TryHalve_id C3) as TH3.
    follow (Overflow_toConfig _ _ _ _ _ _ O12 Z23 TH3 C1 C3).
    eapply Increments_toConfig; eauto 1.
Qed.

Lemma ZIHIO_emb_toConfig k e ne ne' s_1 h_1 s_2 h_2 c1 c2:
  ZIHIO k e ne ->
  embanked ne ne' s_1 h_1 s_2 h_2 ->
  toConfig e c1 ->
  toConfig ne' c2 ->
  c1 -->* c2.
Proof.
  intros HZ He C1 C2.
  inversion HZ; subst.
  destruct (Increments_precond_toConfig I45') as [c5 C5].
  follow (ZIH_toConfig Z12' I23' H34' C1 C5).
  destruct (Overflow_precond_toConfig O56') as [c6 C6].
  epose proof (toConfig_TryHalve_id C6) as TH.
  follow (Increments_toConfig I45' TH C5 C6).
  inversion He; subst.
  inversion Hwemb; subst.
  destruct (Increments_precond_toConfig I45'0) as [c4' C4'].
  follow (OZIH_toConfig O56' Z12'0 I23'0 H34'0 C6 C4').
  destruct n1' as [|n1'].
  - inverts I67.
    apply (Increments_toConfig I45'0 (Halve_TryHalve H56') C4' C2).
  - destruct (Increments_precond_toConfig I67) as [c6' C6'].
    follow (Increments_toConfig I45'0 (Halve_TryHalve H56') C4' C6').
    pose proof (toConfig_TryHalve_id C2) as TH7.
    apply (Increments_toConfig I67 TH7 C6' C2).
Qed.

Lemma ZIHIO_embanked_batch_toConfig {i k e ne ne' h_1 h_2 c1 c2}:
  ZIHIO k e ne ->
  embanked_batch i ne ne' h_1 h_2 ->
  toConfig e c1 ->
  toConfig ne' c2 ->
  c1 -->* c2.
Proof.
  intros HZ Heb C1 C2.
  inversion Heb; subst.
  - eapply ZIHIO_emb_toConfig; eauto 1.
  - eapply ZIHIO_emb_toConfig; eauto 1.
  - destruct (embanked_batch_precond_toConfig Heb0) as [c' C'].
    eapply evstep_trans.
    + eapply ZIHIO_emb_toConfig; eauto 1.
    + eapply embanked_batch_toConfig; eauto 1.
Qed.

Lemma Sk_closed k b c:
  k<>0 ->
  Base k b ->
  toConfig b c ->
  exists b' c',
  Base (S k) b' /\
  toConfig b' c' /\
  c -->* c'.
Proof.
  intros Hk Hb C.
  epose proof (Sk_to_E'' k Hk b Hb) as H.
  destruct H as [e [ne [HN [Heb [HA [Ha [n'ne [Heb' [Hl' [Ha0' [Ha1' [Ha' Ha_last']]]]]]]]]]]].
  destruct (embanked_batch_postcond_toConfig Heb) as [c1 C1].
  epose proof (embanked_batch_toConfig Heb C C1) as c_c1.
  destruct (embanked_batch_precond_toConfig Heb') as [c2 C2].
  epose proof (N'steps_toConfig HN C1 C2) as c1_c2.
  destruct (embanked_batch_postcond_toConfig Heb') as [c3 C3].
  epose proof (embanked_batch_toConfig Heb' C2 C3) as c2_c3.
  eassert _ as X1. {
    apply (E''_Overflow k Hk n'ne).
    1: eexists; eauto 1.
    all: auto 1.
  }
  destruct X1 as [ez HZ].
  destruct (ZIHIO_emb k Hk _ _ HZ) as [nez Hemb].
  destruct (ZIHIO_embanked_batch k Hk _ _ _ HZ Hemb) as [n'ez [Heb'' Heb''_cond]].
  eassert _ as X2. {
    eapply (last_step k _ _ Heb''); tauto.
  }
  destruct X2 as [b' [h_1 [h_2 [Heb''' Hb']]]].
  destruct (embanked_batch_postcond_toConfig Heb'') as [c4 C4].
  epose proof (ZIHIO_embanked_batch_toConfig HZ Heb'' C3 C4) as c3_c4.
  destruct (embanked_batch_postcond_toConfig Heb''') as [c5 C5].
  epose proof (embanked_batch_toConfig Heb''' C4 C5) as c4_c5.
  exists b' c5.
  rewrite add_comm in Hb'.
  rsplit; auto 1.
  follow c_c1.
  follow c1_c2.
  follow c2_c3.
  follow c3_c4.
  apply c4_c5.
Qed.

Lemma base :
  c0 -->*
  lower ([0; 4; 2; 0]).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 205 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Definition Base_1 := (1,[4;2;0]).

Lemma Base_1_spec:
  Base 1 Base_1.
Proof.
  constructor; cbn; auto 1.
  intro i.
  destruct i as [|[|[|[|i]]]]; reflexivity.
Qed.

Lemma Base_1_toConfig:
  toConfig Base_1 (lower [0;4;2;0]).
Proof.
  constructor.
Qed.


Lemma Str_app_inj2{T} (x:list T) xs xs0:
  xs <> xs0 ->
  x *> xs <> x *> xs0.
Proof.
  induction x.
  1: cbn; tauto.
  intro H.
  intro H0.
  cbn in H0.
  inverts H0.
  specialize (IHx H).
  congruence.
Qed.



Lemma lowerL'_inj xs xs0:
  xs <> xs0 ->
  lowerL' xs <> lowerL' xs0.
Proof.
  gen xs0.
  induction xs; intros; destruct xs0 as [|x0 xs0].
  - congruence.
  - intro H0.
    assert (Streams.hd (lowerL' []) = Streams.hd (lowerL' (x0::xs0))) as H1 by congruence.
    unfold lowerL' in H1.
    cbn in H1.
    congruence.
  - intro H0.
    assert (Streams.hd (lowerL' []) = Streams.hd (lowerL' (a::xs))) as H1 by congruence.
    unfold lowerL' in H1.
    cbn in H1.
    congruence.
  - destruct (Nat.eqb_spec a x0).
    + subst.
      assert (xs<>xs0) as H0 by congruence.
      specialize (IHxs _ H0).
      unfold lowerL'. fold lowerL'.
      intro H1.
      inverts H1. gen H3.
      apply Str_app_inj2,IHxs.
    + unfold lowerL'. fold lowerL'.
      intro H1.
      inverts H1.
      clear H.
      gen x0.
      induction a; intros; destruct x0 as [|x0].
      * congruence.
      * cbn in H2.
        destruct xs.
        -- unfold lowerL' in H2. fold lowerL' in H2.
          do 2 rewrite const_unfold in H2.
          inverts H2.
        -- unfold lowerL' in H2. fold lowerL' in H2.
          inverts H2.
      * cbn in H2.
        destruct xs0.
        -- unfold lowerL' in H2. fold lowerL' in H2.
          do 2 rewrite const_unfold in H2.
          inverts H2.
        -- unfold lowerL' in H2. fold lowerL' in H2.
          inverts H2.
      * cbn in H2.
        inverts H2.
        eapply IHa.
        2: apply H0. lia.
Qed.



Lemma Base_ne k b b' c c':
  Base k b ->
  Base (S k) b' ->
  toConfig b c ->
  toConfig b' c' ->
  c<>c'.
Proof.
  intros.
  inverts H.
  inverts H0.
  inverts H1.
  inverts H2.
  cbn in Base_a0',Base_a0'0.
  inverts Base_a0'.
  inverts Base_a0'0.
  cbn in Base_l,Base_l0.
  rewrite grey_to_binary_length,length_map in Base_l,Base_l0.
  unfold lower,lowerL.
  cbn.
  assert (length xs <> length xs0) as H by lia.
  assert (xs<>xs0) as H0 by congruence.
  pose proof (lowerL'_inj _ _ H0) as H1.
  intro H2.
  remember (lowerL' xs) as v1.
  remember (lowerL' xs0) as v2.
  inverts H2.
  destruct v1,v2.
  cbn in H4,H5.
  congruence.
Qed.

Theorem nonhalt:
  ~halts tm c0.
Proof.
  apply (multistep_nonhalt tm c0 (lower [0;4;2;0])).
  1: apply base.
  apply (progress_nonhalt tm (fun c => exists k b, k<>0 /\ Base k b /\ toConfig b c)).
  2: {
    exists 1 Base_1.
    rsplit.
    - congruence.
    - apply Base_1_spec.
    - apply Base_1_toConfig.
  }
  intros c H.
  destruct H as [k [b [Hk [Hb Hc]]]].
  destruct (Sk_closed k b c Hk Hb Hc) as [b' [c' [Hb' [Hc' c_c']]]].
  exists c'.
  split.
  1: exists (S k) b'; rsplit; auto 1.
  apply evstep_progress.
  1: apply c_c'.
  eapply Base_ne with (k:=k); eauto 1.
Qed.







