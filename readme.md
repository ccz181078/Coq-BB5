# Coq-BB5

A Turing machine(TM) has type $St\to\Sigma\to ((St\times\{-1,+1\}\times\Sigma)+\{\bot\})$ , given current state and input, it returns the next state, head moving direction and output; $\bot$ means halt at the next step.

An ExecState has type $St\times (\mathbb{Z}\to\Sigma)$ , means the current state and tape configuration after some steps.

BB(5) is the maximum steps to halt for all TM with $|St|=5$ and $\Sigma=\{0,1\}$ and starts from empty tape.

This is a Coq project for proving BB(5)=47,176,870. **The proof is incomplete now. **

## loop1_decider

This is a trivial decider for one of these situations:

1. The TM halts in at most 47,176,870 steps.
2. The TM reaches an ExecState $0^\infty A(s,x)B0^\infty$ twice.
3. The TM reaches an ExecState $0^\infty CBA(s,x)0^\infty$ , and $\forall C,\;0^\infty CBA(s,x)0^\infty \rightsquigarrow^+ 0^\infty CB^2A(s,x)0^\infty$ .

Here we write an ExecState as a string, $0^\infty A(s,x)B0^\infty$ means current state is $s$ , current input is $x$ , the half-tape to the left(right) of the head is $0^\infty A$ ( $B0^\infty$ ), $A,B,C\dots$ are strings and $x,a,b,c\dots$ are elements of $\Sigma$.

$X\rightsquigarrow^+Y$ means $Y$ is reachable from $X$ after some steps (but not 0 step).

## NGramCPS decider

The idea of this decider is simple:

If we have finite sets $L,R\in\mathcal{P}(\Sigma^n)$ and $M\in\mathcal{P}(St\times \Sigma^{2n+1})$ , and forall reachable ExecState $0^\infty A(s,x)B0^\infty$ , $(s,A[-n:]xB[:n])\in M$ and $\forall m\in\mathrm{N}^+,\;(0^\infty) A[-m-n:-m]\in L,\;(B0^\infty) [m:m+n]\in R$ (":" is in numpy style), then the TM will never halt.

See [Nathan-Fenner/bb-simple-n-gram-cps (github.com)](https://github.com/Nathan-Fenner/bb-simple-n-gram-cps) for more details.

We can save more information on the tape, for example, use a queue of fixed size or a LRU cache to save the update history of each position on the tape.  This is implemented by increasing the size of the charset $\Sigma$ without affect to the TM's haltness. The NGramCPS decider is improved a lot by this way.

`NGramCPS_decider_impl1` use a fixed size queue for update history.

`NGramCPS_decider_impl2` doesn't use update history.

`NGramCPS_LRU_decider` use an LRU cache for update history.

## RepWL_ES_decider

This decider is the special case of CTL deciders ([The 30 to 34 CTL holdouts from BB(5) - Individual machines - The Busy Beaver Challenge (bbchallenge.org)](https://discuss.bbchallenge.org/t/the-30-to-34-ctl-holdouts-from-bb-5/141)).

If we have finite sets $S_1,S_2$ of $\mathrm{RegExp}\times St\times \mathrm{RegExp}$ , and forall reachable ExecState, it can reach an ExecState $0^\infty A(s,x)B0^\infty$ , exists $R_1,R_2\in\mathrm{RegExp}$ , $R_1,R_2$ matches $A,xB$ (or $Ax,B$) and $(R_1,s,R_2)\in S_1$ (or $(R_1,s,R_2)\in S_2$ ), then the TM will never halt.

Regular expressions used in this decider (with parameters $n$ and $m$) are limited to be like $A_1A_2A_3\dots A_{n_0}$ and each $A_i$ is like $B^k$ or $B^mB^*$ , $B$ matches a fixed string of length $n$ , and $1\le k\le m-1$ .

## dfa_nfa_verifier

This decider accepts a DFA as input, and constructs an NFA (the method is described in [Direct recognizer for L(TM/~) ](https://github.com/bbchallenge/bbchallenge-deciders/tree/main/decider-finite-automata-reduction)) to recognize all tape configuration that will halt. The decider then check whether initial tape configuration is accepted, if not, the TM will never halt.

The searching of the DFA is not implemented. DFAs for 23 TMs are listed in the code.

## MITM_WDFA_verifier

This decider accepts two weighted DFA (as described in [Iijil1/MITMWFAR: Testing the feasability of using weighted automatons to describe non-regular languages that solve the halting problem for some turing machines (github.com)](https://github.com/Iijil1/MITMWFAR) ) as input, and use a method similar to RepWL_ES_decider to find a set of ExecState which is closed under step.

The searching of the weighted DFA is not implemented. DFAs for 17 TMs are listed in the code.

## TNF_Node

An TNF_Node records a TM in Tree Normal Form(TNF), and may be replaced with its succesors(update the visited halt transition to non-halt transition) if the TM halts or remove from the search queue if the TM doesn't halt.

The search queue is initialized with one TNF_Node (records the TM with all transitions halt).

The search queue can be updated when an TNF_Node in it is decided to halts or never halts.

When the search queue becomes empty, the conjectured value of BB(5) is proved.

**However, after about 12h of searching, there are 14 non-trivial TMs(13 of them write 1 at the first step) left in the search queue that cannot be decided by the three deciders above, so the proof is incomplete. **

## decider_all

Different deciders are arranged in a specific order to efficiently decide the haltness of most TMs.

A list of about 8,000 TMs are mapped to specific deciders (and parameters). This avoids grid search of decider kind and parameters.

## TODO

The searching result is not proved (and need some trick to avoid compute twice when Qed).

Merge 13 individual TM's proof of nonhalt.

