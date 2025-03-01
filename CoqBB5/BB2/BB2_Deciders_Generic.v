
(**

Enumerative type for the deciders used with generic parameters (i.e. not hardcoded per machine), see BB5_Deciders_Pipeline.v.

Note: this type is isolated because BB5_Enumeration.v and subsequently TNF.v also depend on it in order to report which decider decided which machine.
*)

Inductive DeciderIdentifier : Type :=
| DECIDER_NIL (* Definition HaltDecider_nil:HaltDecider := fun _ => Result_Unknown. *)
| LOOP1_params_6 (* decider2 *)
| NGRAM_CPS_IMPL2_params_1_1_100. (* decider3 *)