# Coq-BB5

A Turing machine(TM) has type $St\to\Sigma\to ((St\times\{-1,+1\}\times\Sigma)+\{\bot\})$ , given current state and input, it returns the next state, head moving direction and output; $\bot$ means halt at the next step.

An ExecState has type $St\times (\mathbb{Z}\to\Sigma)$ , means the current state and tape configuration after some steps.

BB(5) is the maximum steps to halt for all TM with $|St|=5$ and $\Sigma=\{0,1\}$ and starts from empty tape.

This is a Coq project for proving BB(5)=47,176,870. **The proof is incomplete now. **

The main part of the proof is in `BB52Theorem.v` . Most other files are from BusyCoq ([busycoq/verify at master · meithecatte/busycoq (github.com)](https://github.com/meithecatte/busycoq/tree/master/verify)).

## loop1_decider

This is a trivial decider for one of these situations:

1. The TM halts in at most 47,176,870 steps.
2. The TM reaches an ExecState $0^\infty A(s,x)B0^\infty$ twice.
3. The TM reaches an ExecState $0^\infty CBA(s,x)0^\infty$ , and $\forall C,\;0^\infty CBA(s,x)0^\infty \rightsquigarrow^+ 0^\infty CB^2A(s,x)0^\infty$ .

Here we write an ExecState as a string, $0^\infty A(s,x)B0^\infty$ means current state is $s$ , current input is $x$ , the half-tape to the left(right) of the head is $0^\infty A$ ( $B0^\infty$ ), $A,B,C\dots$ are strings and $x,a,b,c\dots$ are elements of $\Sigma$.

$X\rightsquigarrow^+Y$ means $Y$ is reachable from $X$ after some steps (but not 0 step).

`loop1_decider` is the implementation of this method. It simulate the TM execution for $2^k$ steps, and checks whether the (state,input) history has a suffix that repeats at least twice and is case 2 or case 3.

`halt_decider` is a weaker version, only checks for case 1 (halts), and saves a lot of memory because the history ExecState are no longer useful. TMs halts in 4100~47,176,870 steps are listed in `tm_Ha` and decided by this decider.

`halt_verifier` is similar to `halt_decider` , but verify whether the number of steps before halting is the desired value. The lower bound of BB(5) is proved by this verifier.

## NGramCPS decider

The idea of this decider is simple:

If we have finite sets $L,R\in\mathcal{P}(\Sigma^n)$ and $M\in\mathcal{P}(St\times \Sigma^{2n+1})$ , and forall reachable ExecState $0^\infty A(s,x)B0^\infty$ , $(s,A[-n:]xB[:n])\in M$ and $\forall m\in\mathrm{N}^+,\;(0^\infty) A[-m-n:-m]\in L,\;(B0^\infty) [m:m+n]\in R$ (":" is in numpy style), then the TM will never halt.

See [Nathan-Fenner/bb-simple-n-gram-cps (github.com)](https://github.com/Nathan-Fenner/bb-simple-n-gram-cps) for more details.

We can record more information on the tape, for example, use a queue of fixed size or a LRU cache to save the update history of each position on the tape.  This is implemented by increasing the size of the charset $\Sigma$ without affect to the TM's haltness. The NGramCPS decider is improved a lot by this way.

`NGramCPS_decider_impl1` use a fixed size queue for update history (i.e. record the last k updates where k is a constant).

`NGramCPS_decider_impl2` doesn't use update history (and it's faster).

`NGramCPS_LRU_decider` use an LRU cache (i.e. maintain a list of $St\times Σ$ , and for each update $(s,i)$ (current (state,input)) , remove it from the list and push it to the front of the list) for update history.

We use `PositiveMap.tree` (and sometimes together with a list) as the data structure of a finite set/map. `PositiveMap.tree` needs `positive` (bit-string) keys, so some functions named `..._enc` are used to encode elements of other type as bit-string.

## RepWL_ES_decider

This decider is the special case of CTL deciders ([The 30 to 34 CTL holdouts from BB(5) - Individual machines - The Busy Beaver Challenge (bbchallenge.org)](https://discuss.bbchallenge.org/t/the-30-to-34-ctl-holdouts-from-bb-5/141)).

If we have finite sets $S_1,S_2$ of $\mathrm{RegExp}\times St\times \mathrm{RegExp}$ , and forall reachable ExecState, it can reach an ExecState $0^\infty A(s,x)B0^\infty$ , exists $R_1,R_2\in\mathrm{RegExp}$ , $R_1,R_2$ matches $A,xB$ (or $Ax,B$) and $(R_1,s,R_2)\in S_1$ (or $(R_1,s,R_2)\in S_2$ ), then the TM will never halt.

Regular expressions used in this decider (with parameters $n$ and $m$) are limited to be like $A_1A_2A_3\dots A_{n_0}$ and each $A_i$ is like $B^k$ or $B^mB^*$ , $B$ matches a fixed string of length $n$ , and $1\le k\le m-1$ .

For example, when n=2, m=3, the tape will be divide into blocks of length n, and erase the information of more than m repeats, like `...00000101010111 <A 10101111110000...` =>  `...00 00 01 01 01 01 11 <A 10 10 11 11 11 00 00...` => `(01)^3+ (11)^1 <A (10)^2 (11)^3+`  , here `01^3+`  matches `01^3, 01^4, 01^5, ...`  and `11 <A 10` (directed head notation) means `1(A,1)10` .

For an abstracted ExecState represented as $\mathrm{RegExp}\times St\times \mathrm{RegExp}$ , we can run it for a macro-step (until the head leave current block (or timeout)). The decider will extend $S_1,S_2$ in this way until they are closed under macro-step (or timeout). The two regular expressions in an abstracted ExecState can be viewed as two stacks, a macro-step pops a block from a stack, and then push the updated block into a stack. Pop is like `(01)^3+ => (01,(01)^3+),(01,(01)^2);  (01)^2 => (01,(01)^1);  (01)^1 => (01,) ` , push is the reversed procedure of pop.

## dfa_nfa_verifier

This decider accepts a DFA as input, and constructs an NFA (the method is described in [Direct recognizer for L(TM/~) ](https://github.com/bbchallenge/bbchallenge-deciders/tree/main/decider-finite-automata-reduction)) to recognize all tape configuration that will halt. The decider then check whether initial tape configuration is accepted, if not, the TM will never halt.

The searching of the DFA is not implemented. DFAs for 23 TMs are listed in `tm_DNV`.

## MITM_WDFA_verifier

This decider accepts two weighted DFA (as described in [Iijil1/MITMWFAR: Testing the feasability of using weighted automatons to describe non-regular languages that solve the halting problem for some turing machines (github.com)](https://github.com/Iijil1/MITMWFAR) ) as input, and use a method similar to RepWL_ES_decider to find a set of ExecState which is closed under step.

The searching of the weighted DFA is not implemented. DFAs for 17 TMs are listed in `tm_WA`.

## Translate

This module translates theorems of nonhalt from the proof in BusyCoq/verify.

Skelet1.v takes about 10min.

## TNF_Node

An TNF_Node records a TM in Tree Normal Form(TNF), and may be replaced with its succesors(update the visited halt transition to non-halt transition) if the TM halts or remove from the search queue if the TM doesn't halt.

The search queue is initialized with one TNF_Node (records the TM with all transitions halt).

The search queue can be updated when an TNF_Node in it is decided to halts or never halts.

When the search queue becomes empty, the conjectured value of BB(5) is proved.

After using some symmetries (move right at the first step; all unused states are equal) to reduce the search space, there are about 1.6e8 TMs to be decided. Writes 1 at the first step is not used because it may change halting time, and only 1/3 speedup. If a TM writes 0 at the first step, it may be normalized to write 1 at the first step ( implemented in `TM_to_NF` ) and re-run some of the deciders for proving non-halt.

There are some repeated code like `Time Definition q_183 := Eval vm_compute in q_183_def.` . This is used to split the searching process into multiple smaller steps (without this you will wait for hours without any feedback).

**It takes about 12h to clear the search queue. The non-halt of Skelet17 is axiom now, so the proof is incomplete. **

## decider_all

Different deciders are arranged in a specific order to decide most TMs efficiently.

A list of about 8,000 TMs are mapped to specific deciders (and parameters). This avoids grid search of decider kind and parameters.

## TODO

Skelet17's proof of nonhalt.

## Used Axioms

```
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p), x = eq_rect p Q x p h
LEM : forall P : Prop, P \/ ~ P
```

`Eqdep.Eq_rect_eq.eq_rect_eq` is for proving some properties of the bounded natural number type `nat_n` (used by tactics like `dependent destruction`).

`functional_extensionality_dep` is used to simplify the equality between `TM` and between `ExecState` since they are represented by functions, removing this axiom will make setoid everywhere.

`LEM` can simplify some case analysis, and is easy to remove if needed.

