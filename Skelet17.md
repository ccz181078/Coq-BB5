# Skelet17

This document is about the Coq proof of Skelet17 doesn't halt.

For simplicity, only the non-trivial lemmas and definitions in `Skelet.v` are shown. The natural language explaination only talks about some high-level ideas and doesn't talk about the details in the proof.

The proof is complicated due to 6 layers of nested induction.

## level 0 behavior

The transition table of Skelet17:

```
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => None
  | B, 0 => Some (0, L, C)  | B, 1 => Some (1, R, E)
  | C, 0 => Some (0, L, D)  | C, 1 => Some (1, L, C)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, B)
  | E, 0 => Some (0, R, B)  | E, 1 => Some (0, R, A)
  end.
```



level 0 behavior consist of a constant number of steps. They are not written as Lemmas in Coq (but reprove them whenever used).

```
go left (pass 1):
1 <C
----
<C 1


go left (pass 10^2):
1010 <C 
--------
101 <D 0
--------
10 <B 10
--------
1 <C 010
--------
 <C 1010


go left (turn back):
110 <C
-------
11 <D 0
-------
1 <B 10
-------
1 E> 10
-------
10 A> 0
-------
101 B>


go right (pass 10):
 B> 10
------
1 E> 0
------
10 B>


go right (pass 1 10):
 B> 110
-------
1 E> 10
-------
10 A> 0
-------
101 B> 


go right (turn back):
B> 0
----
<C 0



...
```



## level 1 behavior

Using level 0 behavior on `10` repeaters, we have:

```
goright_10:
B> 10^n
-------
10^n B>

goleft_even10:
1010^n <C
---------
<C 1010^n

goleft_odd10:
1 10 1010^n <C
--------------
10 1 1010^n B>
```





## level 2 behavior

We use `lower [a[0]; a[1]; ...; a[l-1]]` to represent `10^a[l-1] ... 1 10^a[1] 1 10^a[0] <C` (i.e. some `10` repeaters seperated by `1` , and the head is at right).

`a++b` is list concat.

`a::b` is concat an element a with list b.

Using level 1 behavior on `lower ...` , we have:

```ocaml
Lemma increment_S_even : forall x xs y z zs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (S x :: xs ++ y :: z :: zs) -->*
  lower (x :: xs ++ y :: S z :: zs).

Lemma increment_S_odd : forall x y xs,
  Odd (S x) ->
  lower (S x :: y :: xs) -->*
  lower (x :: S y :: xs).

Lemma increment_O : forall xs y z zs,
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  lower (O :: xs ++ y :: z :: zs) -->*
  lower (xs ++ y :: S z :: zs).

Lemma overflow_S : forall x xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Odd y ->
  lower (S x :: xs ++ [y]) -->*
  lower (x :: xs ++ [S y; 1; 0; 0]%nat).

Lemma overflow_O : forall xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Odd y ->
  lower (O :: xs ++ [y]) -->*
  lower (xs ++ [S y; 1; 0; 0]%nat).

Lemma zero_S : forall x xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even (S x) ->
  Even y ->
  lower (S x :: xs ++ [y]) -->*
  lower (x :: xs ++ [S y; 0; 0]%nat).

Lemma zero_O : forall xs y,
  Forall Nonzero xs ->
  Forall Even xs ->
  Even y ->
  lower (O :: xs ++ [y]) -->*
  lower (xs ++ [S y; 0; 0]%nat).

```



While the `_O` rules are similar, we can split them into two rules. With some minor changes in the representation, we have:

```
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
```



`TryHalve` is apply `Halve` when possible, and do nothing otherwise.

```
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
```



We can define the translation between `increment/zero/overflow` and `Increment/Halve/Zero/Overflow`.

`toConfig` is the translation between the two different representations of tape config:

```
Inductive toConfig: (nat*(list nat))->(Q*tape)->Prop :=
| toConfig_intro x xs:
  toConfig (S x,xs) (lower (x::xs))
.
```



```ocaml
Lemma Increment_toConfig s1 s2 s3 c1 c3:
  Increment s1 s2 ->
  TryHalve s2 s3 ->
  toConfig s1 c1 ->
  toConfig s3 c3 ->
  c1 -->* c3.

Lemma Zero_toConfig s1 s2 s3 c1 c3:
  Zero s1 s2 ->
  TryHalve s2 s3 ->
  toConfig s1 c1 ->
  toConfig s3 c3 ->
  c1 -->* c3.

Lemma Overflow_toConfig s1 s2 s3 s4 c1 c4:
  Overflow s1 s2 ->
  Zero s2 s3 ->
  TryHalve s3 s4 ->
  toConfig s1 c1 ->
  toConfig s4 c4 ->
  c1 -->* c4.

```



## level 3 behavior

When a series of `Increment` is applied, the mod 2 suffix xor sum of the list form a binary counter (i.e. the value in the list mod 2 form a Grey code counter).

`n` is the current value of the counter, and is updated to `n+(if s then 1 else -1)`  by an `Increment` .

`l` is the number of digits in the counter, `n` is limited in `[0,2^l-1]` .

```ocaml
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
```



Then it's not hard to know the change of `n,s,l` after `Increment/Halve/Zero/Overflow`.

```ocaml
(* s after Inc/Halve/Zero/Overflow *)

Lemma Increment_sgn {s1 s2}:
  Increment s1 s2 ->
  to_s s1 = to_s s2.

Lemma Halve_sgn {s1 s2}:
  Halve s1 s2 ->
  negb (to_s s1) = (to_s s2).

Lemma Zero_sgn {s1 s2}:
  Zero s1 s2 ->
  (to_s s2) = false.

Lemma Overflow_sgn {s1 s2}:
  Overflow s1 s2 ->
  (to_s s2) = false.


(* n after Inc/Halve/Zero/Overflow *)

Lemma Increment_n {s1 s2}:
  Increment s1 s2 ->
  if to_s s1 then
  S (to_n s1) = to_n s2
  else
  to_n s1 = S (to_n s2).

Lemma Halve_n {s1 s2}:
  Halve s1 s2 ->
  div2 (to_n s1) = to_n s2.

Lemma Zero_n {s1 s2}:
  Zero s1 s2 ->
  to_n s2 = (2 ^ (to_l s1)) - 1.

Lemma Overflow_n {s1 s2}:
  Overflow s1 s2 ->
  to_n s2 = O.


(* l after Inc/Halve/Zero/Overflow *)

Lemma Increment_len {s1 s2}:
  Increment s1 s2 ->
  to_l s1 = to_l s2.

Lemma Halve_len {s1 s2}:
  Halve s1 s2 ->
  to_l s1 = S (to_l s2).

Lemma Zero_len {s1 s2}:
  Zero s1 s2 ->
  to_l s2 = to_l s1 + 2.

Lemma Overflow_len {s1 s2}:
  Overflow s1 s2 ->
  to_l s2 = to_l s1 + 1.

```





We use `divpow2r` to track how much times a digit is updated during a series of `Increment` operations.

```ocaml
Definition divpow2r(n i:nat) :=
  (n+(2^i))/(2^(i+1)).
```



Define `Increments` as a series of `Increment` operations:

```ocaml
Inductive Increments: nat->(nat*(list nat))->(nat*(list nat))->Prop :=
| Increments_O s: Increments O s s
| Increments_S n s1 s2 s3:
  Increment s1 s2 ->
  Increments n s2 s3 ->
  Increments (S n) s1 s3
.
```



The change of `ai` after `Increments/Halve/Zero/Overflow`:

```ocaml
Definition ai(i:nat)(s:nat*(list nat)) :=
  nth i (snd s) O.

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

Lemma Increments_a0 {n s1 s2}:
  Increments n s1 s2 ->
  if to_s s1 then
    (fst s1) + (to_n s1) =
    (fst s2) + (to_n s2)
  else
    (fst s2) + (to_n s1) =
    (fst s1) + (to_n s2).

Lemma Zero_a0 {s1 s2}:
  Zero s1 s2 ->
  fst s1 = S (fst s2).

Lemma Zero_a1 {s1 s2}:
  Zero s1 s2 ->
  to_l s1 >= 3 ->
  ai O s1 = ai O s2.

Lemma Zero_a {s1 s2}:
  Zero s1 s2 ->
  forall i, ai i s1 + (if Nat.eqb i (to_l s1 - 1) then 1 else 0)%nat = ai i s2.

Lemma Overflow_a0 {s1 s2}:
  Overflow s1 s2 ->
  fst s1 = fst s2.

Lemma Overflow_a {s1 s2}:
  Overflow s1 s2 ->
  forall i, ai i s1 + (if Nat.eqb i (to_l s1 - 1) then 1 else 0)%nat = ai i s2.

Lemma Halve_a0 {s1 s2}:
  Halve s1 s2 ->
  fst s2 = S (ai O s1).

Lemma Halve_a {s1 s2}:
  Halve s1 s2 ->
  forall i, ai i s2 = ai (S i) s1.
```



The changes of `n,s,l` after `Increments`:

```ocaml
Lemma Increments_sgn {n s1 s2}:
  Increments n s1 s2 ->
  to_s s1 = to_s s2.

Lemma Increments_n {n s1 s2}:
  Increments n s1 s2 ->
  if to_s s1 then
    to_n s1 + n = to_n s2
  else
    to_n s1 = to_n s2 + n.

Lemma Increments_len {n s1 s2}:
  Increments n s1 s2 ->
  to_l s1 = to_l s2.
```



While some cases is not covered by `Increment/Halve/Zero/Overflow` , we need to ensure this will not happen.

`WF1` and `WF2` are two types of config, we track the transition between them to ensure `(x,xs ++ [O; O])` with `Forall Even xs` is unreachable.

```ocaml
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
```

Then we talk about pre-conditions of `Increment/Halve/Zero/Overflow`.

```ocaml

(* more pre-cond to keep post-cond also WF;
   also track the transition between WF1,WF2 *)
Lemma Increment_inc_precond1 {s1}:
  WF1 s1 ->
  to_s s1 = true ->
  to_n s1 < 2^(to_l s1) - 1 ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF1 s2.


Lemma Increment_inc_precond22 {s1}:
  WF2 s1 ->
  to_s s1 = true ->
  to_n s1 < 2^(to_l s1 - 2) - 1 ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF2 s2.

Lemma Increment_inc_precond21 {s1}:
  WF2 s1 ->
  to_s s1 = true ->
  to_n s1 = 2^(to_l s1 - 2) - 1 ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF1 s2.

Lemma Increment_dec_precond1 {s1}:
  WF1 s1 ->
  to_s s1 = false ->
  to_n s1 > O ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF1 s2.

Lemma Increment_dec_precond2 {s1}:
  WF2 s1 ->
  to_s s1 = false ->
  to_n s1 > S O ->
  fst s1 > O ->
  exists s2, Increment s1 s2 /\ WF2 s2.

Lemma Halve_precond1 {s1}:
  WF1 s1 ->
  fst s1 = O ->
  to_l s1 >= 2 ->
  exists s2, Halve s1 s2 /\ WF1 s2.

Lemma Halve_precond2 {s1}:
  WF2 s1 ->
  fst s1 = O ->
  (to_n s1 <> S O) ->
  exists s2, Halve s1 s2 /\ WF2 s2.

Lemma Zero_precond {s1}:
  WF1 s1 ->
  to_s s1 = false ->
  to_n s1 = O ->
  exists s2, Zero s1 s2 /\ WF2 s2.

Lemma Overflow_precond {s1}:
  WF1 s1 ->
  to_s s1 = true ->
  to_n s1 = 2^(to_l s1) - 1 ->
  fst s1 = 1 ->
  exists s2, Overflow s1 s2 /\ WF1 s2.

```



pre-conditions for `Increments`:

```ocaml
Lemma Increments_inc_precond1 {s1} n:
  WF1 s1 ->
  to_s s1 = true ->
  to_n s1 + n < 2^(to_l s1) ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF1 s2.

Lemma Increments_inc_precond2 {s1} n:
  WF2 s1 ->
  to_s s1 = true ->
  to_n s1 + n >= 2^(to_l s1 - 2) ->
  to_n s1 + n < 2^(to_l s1) ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF1 s2.

Lemma Increments_dec_precond1 {s1} n:
  WF1 s1 ->
  to_s s1 = false ->
  to_n s1 >= n ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF1 s2.

Lemma Increments_dec_precond2 {s1} n:
  WF2 s1 ->
  to_s s1 = false ->
  to_n s1 >= S n ->
  fst s1 >= n ->
  exists s2, Increments n s1 s2 /\ WF2 s2.
```



## level 4 behavior

Using pre-conditions and the update rules of `ai,n,s,l` of `Increments/Halve/Zero`, we can find the pre-conditions and effects for `wealky_embanked` (i.e. `Zero,Increments(s=false),Halve,Increments(s=true),Halve`); and `embanked` (i.e. `wealky_embanked,Increments(s=false),Zero, undo Zero` ).

```ocaml
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
```



```ocaml
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


Lemma embanked_precond {s1 s6 s_1 h_1 s_2 h_2}:
  weakly_embanked s1 s6 s_1 h_1 s_2 h_2 ->
  h_2 <= fst s6 ->
  exists s7, embanked s1 s7 s_1 h_1 s_2 h_2.

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


Fixpoint ctz(x:positive):nat :=
match x with
| xO x0 => S (ctz x0)
| _ => O
end.

Definition ctzS(n:nat):nat :=
  ctz (Pos.of_succ_nat n).

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
```

When `embanked` satifies `Add2 i` , the next `weakly_embanked` can be replaced by `embanked` , and the update of `h_1,h_2` of the next `embanked` is simple.

Acturally, all reachable `embanked` operations satisfies `Add2 i`.

## level 5 behavior

`embanked_batch` is a series of `embanked` with the `i` in  `Add2 i` decrease to 0 or 1.

`embanked` and `Add2 i` can derive `embanked_batch` directly.

For example, an `embanked` with `Add2 i, i=10` can derive a sequence of `embanked` with `i=8,6,4,2,0` after it. These `embanked` with `i=10,8,6,4,2,0` form a `embanked_batch` with `i=10`.

`Add2s i` describes the effect to `ai'` of `embanked_batch`.

```ocaml
Inductive Add2s: nat->(nat*(list nat))->(nat*(list nat))->Prop :=
| Add2s_intro i0 s1 s2
  (Hadd2s:forall i, ai' i s1 + (if andb (i <=? i0) (Bool.eqb (even i) (even i0)) then 2 else 0)%nat = ai' i s2):
  Add2s i0 s1 s2
.

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

Lemma embanked__embanked_batch {i}:
  forall {e ne s_1' h_1' s_2' h_2'},
  embanked e ne s_1' h_1' s_2' h_2' ->
  Add2 i e ne ->
  exists n'e, embanked_batch i e n'e h_1' h_2'.

Lemma embanked_batch_last {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  exists e',
  embanked_batch (i mod 2) e' ne h_1 h_2.

Lemma embanked_batch_Add2s {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  Add2s i e ne.

Lemma embanked_batch_precond {i e ne ne' h_1 h_2 s_1' h_1' s_2' h_2'}:
  embanked_batch i e ne h_1 h_2 ->
  weakly_embanked ne ne' s_1' h_1' s_2' h_2' ->
  exists n'ne, embanked_batch (match i mod 2 with
  | O => (ctzS (h_1-1))
  | S O => (S (ctzS h_2))
  | S (S _) => 0
  end) ne n'ne h_1' h_2'.

Lemma embanked_batch_postcond {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  WF1 ne /\
  to_s ne = false /\
  to_n ne = 0 /\
  to_l ne >=3 /\
  Odd (fst ne).

Lemma embanked_batch__wemb {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  ai' 0 ne < 2^(to_l ne) - 1 ->
  ai' 1 ne < 2^(to_l ne - 1)*3 ->
  exists ne0 s_1' s_2' h_1' h_2',
  weakly_embanked ne ne0 s_1' h_1' s_2' h_2'.

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

Lemma embanked_batch_len {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  to_l e = to_l ne.

Lemma embanked_batch_a0_a1 {i e ne h_1 h_2}:
  embanked_batch i e ne h_1 h_2 ->
  ai' 0 ne = ai' 0 e + (1-(i mod 2))*2 /\
  ai' 1 ne = ai' 1 e + ((i mod 2))*2.

```

`embanked_batch` changes `ai' 0` and `ai' 1` by 0 or 1 depend on the parity of  `i`, and if `ai' 0, ai' 1` are not too large, `embanked_batch` can be performed again.

## level 6 behavior

`Base` is something like `lower [0; 2^2k; 2^2k-1; ...; 4; 2; 0]`.

`N'steps` is a series of `embanked_batch`.

`ZIHIO` (`Zero,Increments(s=false),Halve,Increments(s=true),Overflow`) is the only reachable case that doesn't follow the `embanked`  (and satisfies `Add2 i`) pattern.

`Base k` is updated to `Base (k+1)` after some operations, this leads to the proof of nonhalt.



The `i` of a series of `embanked_batch` looks like (read from left to right):

```
12  1312    14  12  1312    1512    1312    14  12  1312    16  ...
  01    0201  03  01    0201    0401    0201  03  01    0201  05...
```

The first line means `h_2` is increased by 1, the second line means `h_1` is decreased by 1.

When the parity of `i` is changed, it switch from one line to another line.

If we only look at one line, it has a fractal structure `1, 121, 1213121, 121312141213121, ...` generated by `ctzS`.

The `i,h_1,h_2` of an `embanked_batch` depend on the `i mod 2,h_1,h_2` of last `embanked_batch` (as shown in `embanked_batch_precond'`). The `i` in the first line depend on `ctzS h_2`, and the `i` in the second line depend on `ctzS (h_1-1)`.

While `ctzS(2^(k*2)+i) = ctzS(2^(k*2-i-2))`, the two lines are synchronized (after 4 or 8 `embanked_batch`) if `h_1,h_2` are initialized properly. This enable us to derive an `N'steps` to update `h_1,h_2` from `2^(k*2)-1,2^(k*2)` (after one `embanked_batch` from `Base k`) to `2^(k*2)-1-m,2^(k*2)+m` when `ctzS (m-1)` is odd and `m<=2^(k*2)-2`. This structure also change `ai'` in a predictable way.



```ocaml

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

Lemma Base_embanked_batch {e}:
  Base e ->
  exists ne,
  embanked_batch (k*2+1) e ne (2^(k*2)-1) (2^(k*2)) /\
  to_l ne = k*2+1 /\
  ai' 0 ne = 1 /\
  ai' 1 ne = 2^(k*2)+2 /\
  Add2s (k*2+1) e ne.

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

Lemma ZIHIO_emb e ne:
  ZIHIO e ne ->
  exists ne',
  embanked ne ne' (2^(k*2+3)-1) (2^(k*2+2)-1) (2^(k*2+3)-4) (2^(k*2+2)-2).

Lemma ZIHIO_emb_Add2 e ne ne':
  ZIHIO e ne ->
  embanked ne ne' (2^(k*2+3)-1) (2^(k*2+2)-1) (2^(k*2+3)-4) (2^(k*2+2)-2) ->
  Add2 (k*2+1) ne ne'.

Lemma ZIHIO_embanked_batch e ne ne':
  ZIHIO e ne ->
  embanked ne ne' (2^(k*2+3)-1) (2^(k*2+2)-1) (2^(k*2+3)-4) (2^(k*2+2)-2) ->
  exists n'ne,
  embanked_batch (k*2+1) ne n'ne (2^(k*2+2)-1) (2^(k*2+2)-2) /\
  to_l n'ne = k*2+3 /\
  ai' 0 n'ne = 1 /\
  ai' 1 n'ne = 2^(k*2+2)-2 /\
  (forall i, 2<=i -> ai' i n'ne = if i<? k*2+3 then 2^(k*2+3-i) else 0).

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

```

We reach `Base (k+1)` from `Base k` by `embanked_batch, N'_steps, embanked_batch, ZIHIO, embanked_batch`.

## level 7 behavior

`Base 1` is reachable from empty tape after 205 steps.

```ocaml

Lemma Sk_closed k b c:
  k<>0 ->
  Base k b ->
  toConfig b c ->
  exists b' c',
  Base (S k) b' /\
  toConfig b' c' /\
  c -->* c'.

Lemma base :
  c0 -->*
  lower ([0; 4; 2; 0]).

Definition Base_1 := (1,[4;2;0]).

Lemma Base_1_spec:
  Base 1 Base_1.

Lemma Base_1_toConfig:
  toConfig Base_1 (lower [0;4;2;0]).

Lemma Base_ne k b b' c c':
  Base k b ->
  Base (S k) b' ->
  toConfig b c ->
  toConfig b' c' ->
  c<>c'.

Theorem nonhalt:
  ~halts tm c0.

```

