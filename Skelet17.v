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
  rewrite grey_to_binary_length,map_length,app_length.
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
    repeat rewrite grey_to_binary_length,map_length,app_length.
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
  repeat rewrite grey_to_binary_length,map_length,app_length.
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
  repeat rewrite grey_to_binary_length,map_length,app_length.
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
      rewrite app_length.
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
      assert (E2:length ((xs ++ [y]) ++ [S z])=S sl) by (rewrite app_length; cbn; lia).
      assert (E3:length ((xs ++ [y]) ++ [z])=S sl) by (rewrite app_length; cbn; lia).
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
      rewrite app_length.
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
      assert (E2:length ((xs ++ [y]) ++ [S z])=S sl) by (rewrite app_length; cbn; lia).
      assert (E3:length ((xs ++ [y]) ++ [z])=S sl) by (rewrite app_length; cbn; lia).
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

Inductive Step: (nat*(list nat))->(nat*(list nat))->Prop :=
| IncrementStep s1 s2: Increment s1 s2 -> Step s1 s2
| HalveStep s1 s2: Halve s1 s2 -> Step s1 s2
| ZeroStep s1 s2: Zero s1 s2 -> Step s1 s2
| OverflowStep s1 s2: Overflow s1 s2 -> Step s1 s2
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


Lemma WF_Step s1:
  WF s1 ->
  exists s2, Step s1 s2.
Proof.
  intro Hwf.
  inverts Hwf as Hwf.
  - inverts Hwf.
    destruct x as [|x].
    { destruct xs;
        eexists; apply HalveStep; econstructor. }
    destruct (Even_or_Odd x) as [Ex|Ox].
    {
      destruct (Forall_Even_dec xs) as [H0|[xs0 [y0 [zs [H0 [H1 H2]]]]]].
      - destruct (Even_or_Odd y) as [H1|H1].
        + eexists. apply ZeroStep. econstructor; eauto 1.
        + eexists. apply OverflowStep. econstructor; eauto 1.
      - rewrite H2.
        rewrite <-app_assoc. cbn.
        destruct zs;
          cbn;
          eexists; apply IncrementStep;
          eapply Increment_even; eauto 1;
          rewrite H2 in H;
          rewrite Forall_app in H;
          apply H.
    }
    {
      destruct xs;
        cbn;
        eexists; apply IncrementStep;
        eapply Increment_odd; eauto 1.
    }
  - inverts Hwf.
    destruct x as [|x].
    { destruct xs;
        eexists; apply HalveStep; econstructor. }
    destruct (Even_or_Odd x) as [Ex|Ox].
    {
      destruct zs;
        eexists; apply IncrementStep; eapply Increment_even; eauto 1.
    }
    {
      destruct xs; cbn;
        eexists; apply IncrementStep; eapply Increment_odd; eauto 1.
    }
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
    rewrite grey_to_binary_length,map_length,app_length in H,IHxs.
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
  rewrite grey_to_binary_length,map_length.
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
  rewrite app_length.
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
        rewrite (grey_to_binary_length),map_length,app_length.
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
        rewrite grey_to_binary_length,map_length,app_length in H1.
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
    rewrite grey_to_binary_length,map_length in H1'.
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

Inductive weakly_embanked: (nat*(list nat))->(nat*(list nat))->nat->nat->nat->nat->Prop :=
| weakly_embanked_intro n1' n2' s1' s2' s3' s4' s5' s6'
  (Z12':Zero s1' s2')
  (I23':Increments n1' s2' s3')
  (H34':Halve s3' s4')
  (I45':Increments n2' s4' s5')
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

  (n3_expr:(to_n s3') + (fst s1') = 2^(to_l s1'))
  (n4_expr:(to_n s4') + (fst s1')/2 + 1 = 2^(to_l s1' - 1))
  (n5_expr:(to_n s5') = (ai O s1') + 2^(to_l s1' - 1))
  (n6_expr:(to_n s6') = (ai O s1')/2 + 2^(to_l s1' - 2))

  (a60_expr:ai 1 s1' + 2 ^ (to_l s1' - 2) + divpow2r (to_n s5') 0 + 1 =
  fst s6' + divpow2r (to_n s4') 0 + divpow2r (to_n s3') 1)

  (a6_expr:forall i : nat,
    ai (S (S i)) s1' + (if S (S i) =? to_l s1' - 1 then 1 else 0) + divpow2r (to_n s2') (S (S i)) +
    divpow2r (to_n s5') (S i) = ai i s6' + divpow2r (to_n s4') (S i) + divpow2r (to_n s3') (S (S i))):

  weakly_embanked s1' s6' (to_n s3') (to_n s4') (to_n s5') (to_n s6').



Inductive embanked: (nat*(list nat))->(nat*(list nat))->nat->nat->nat->nat->Prop :=
| embanked_intro n1' s1' s6' s7' s8' s_1' h_1' s_2' h_2'
  (Hwemb:weakly_embanked s1' s6' s_1' h_1' s_2' h_2')
  (I67:Increments n1' s6' s7')
  (Z78:Zero s7' s8')
  (Hwf7:WF1 s7')
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
  rewrite grey_to_binary_length,map_length,app_length.
  cbn.
  replace (length xs + 1 - 1) with (length xs) by lia.
  destruct (Nat.eqb_spec i (length xs)) as [E|E].
  - subst i. do 2 rewrite nth_middle.
    lia.
  - assert (i<length xs\/i>length xs) as [E0|E0] by lia.
    + do 2 (rewrite app_nth1; auto 1).
    + rewrite app_nth2. 2: lia.
      rewrite app_nth2. 2: lia.
      destruct (i-length xs) as [|v1] eqn:E1. 1: lia.
      cbn.
      destruct v1 as [|v1].
      1: reflexivity.
      destruct v1 as [|v1].
      1: reflexivity.
      destruct v1 as [|v1].
      1,2: reflexivity.
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
  weakly_embanked s1 s2 s_1 s_2 h_1 h_2.
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
  ai 1 s1 + divpow2r n2 1 + divpow2r n5 0 + 1 =
  a60 + divpow2r n4 0 + divpow2r n3 1). {
    specialize (Hs5a_expr O).
    destruct (Nat.eqb_spec 1 (l1-1)).
    1: lia.
    rewrite add_0_r in Hs5a_expr.
    rewrite Hs6a0.
    lia.
  }
  replace (divpow2r n2 1) with (2 ^ (l1 - 2)) in Ha60_expr. 2:{
    unfold divpow2r.
    rewrite Hs2n.
    change (2^(1+1)) with 4.
    change (2^1) with 2.
    pose proof (pow2_nez l1).
    replace (2^l1-1+2) with (2^l1+1) by lia.
    replace (2^l1) with (2^((l1-2)+2)) by (f_equal; lia).
    rewrite pow_add_r.
    rewrite div_add_l. 2: congruence.
    rewrite add_0_r.
    reflexivity.
  }
  assert (Hs6a_expr:forall i,
  ai (S (S i)) s1 + (if S (S i) =? l1 - 1 then 1 else 0) + divpow2r n2 (S (S i)) + divpow2r n5 (S i) =
  ai i s6 + divpow2r n4 (S i) + divpow2r n3 (S (S i))). {
    intro i.
    specialize (Hs2a (S (S i))).
    specialize (Hs3a (S (S i))).
    specialize (Hs4a (S i)).
    specialize (Hs5a (S i)).
    specialize (Hs6a i).
    subst.
    lia.
  }
  subst.
  do 5 eexists.
  econstructor.
  - apply Z12.
  - apply I23.
  - apply H34.
  - apply I45.
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
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - apply Ha60_expr.
  - apply Hs6a_expr.
Qed.

Lemma embanked_precond s1 s6 s_1 h_1 s_2 h_2:
  weakly_embanked s1 s6 s_1 h_1 s_2 h_2 ->
  h_2 <= fst s6 ->
  exists s7, embanked s1 s7 s_1 h_1 s_2 h_2.
Proof.
  intros Hweb Hn6_le.
  inversion Hweb; subst.

  eassert (I67:_). {
    apply (Increments_dec_precond1 (to_n s6) Hwf6' Hs6s); lia.
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
  exists s7.
  econstructor.
  - econstructor; eauto 1.
  - apply I67.
  - apply Z78.
  - apply Hwf7.
  - lia.
Qed.




Lemma div2_add2 a:
  (a+2)/2 = a/2+1.
Proof.
  replace (a+2) with (1*2+a) by lia.
  rewrite div_add_l. 2: congruence.
  lia.
Qed.

(* Lemma 3.5 *)
Lemma emb_wemb_s_h e ne nne i s_1 h_1 s_2 h_2 s_1' h_1' s_2' h_2':
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













Lemma halt_case : forall x xs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even x ->
  exists c1,
  lower (x :: xs ++ [O; O]) -->*
  c1 /\ halted tm c1.
Proof.
  introv Hxsnz Hxsev Hx.
  destruct (rev xs) eqn:E.
  - destruct x as [|x].
    + eexists. split.
      * follow (goleft_even (O::xs)).
        repeat evstep1.
        unfold lowerL,lowerL'.
        rewrite E.
        cbn. unfold lowerR'. cbn.
        repeat evstep1.
        finish.
      * constructor.
    + eexists. split.
      * follow (goleft_even (S x::xs)).
        repeat evstep1.
        unfold lowerL,lowerL'.
        rewrite E.
        cbn. unfold lowerR'. cbn.
        repeat evstep1.
        finish.
      * constructor.
  - destruct n as [|n].
    + pose proof (Forall_rev Hxsnz) as H.
      rewrite E in H.
      inverts H as H1 H2. congruence.
    + eexists. split.
      * follow (goleft_even (x::xs)).
        repeat evstep1.
        unfold lowerL,lowerL'.
        cbn.
        rewrite <-app_assoc.
        cbn.
        rewrite E.
        cbn.
        repeat evstep1.
        finish.
      * constructor.
Qed.


Lemma base :
  c0 -->*
  lower ([0; 4; 2; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 205 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base' :
  c0 -->*
  lower ([4; 2; 1; 0; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 240 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base'1 :
  c0 -->*
  lower ([3; 2; 1; 1; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 274 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base'2 :
  c0 -->*
  lower ([2; 3; 1; 1; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 288 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base'3 :
  c0 -->*
  lower ([1; 3; 2; 1; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 312 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.


Lemma base'5 :
  c0 -->*
  lower ([4; 2; 1; 1]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 355 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'6 :
  c0 -->*
  lower ([3; 2; 1; 2]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 389 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'7 :
  c0 -->*
  lower ([2; 3; 1; 2]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 403 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'8 :
  c0 -->*
  lower ([1; 3; 2; 2]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 427 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'9 :
  c0 -->*
  lower ([0; 4; 2; 2]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 433 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma base'10 :
  c0 -->*
  lower ([4; 2; 3; 0; 0]%nat).
Proof.
  unfold lower,lowerL,lowerR,lowerR'.
  cbv[lowerL'].
  cbn.
  do 476 evstep1.
  unfold s0.
  rewrite <-const_unfold.
  finish.
Qed.

Lemma halt_case_1 :
  halts tm (lower ([4; 4; 0; 0]%nat)).
Proof.
  unfold halts.
  eexists.
  unfold halts_in.
  eexists.
  split.
  - repeat evstep1.
    constructor.
  - constructor.
Qed.


