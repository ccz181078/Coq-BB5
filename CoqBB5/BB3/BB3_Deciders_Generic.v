
(**

Enumerative type for the deciders used with generic parameters (i.e. not hardcoded per machine), see BB5_Deciders_Pipeline.v.

Note: this type is isolated because BB5_Enumeration.v and subsequently TNF.v also depend on it in order to report which decider decided which machine.
*)

Inductive DeciderIdentifier : Type :=
| DECIDER_NIL (* Definition HaltDecider_nil:HaltDecider := fun _ => Result_Unknown. *)
| LOOP1_params_21 (* decider2 *)
| NGRAM_CPS_IMPL2_params_1_1_100 (* decider3 *)
| NGRAM_CPS_IMPL2_params_2_2_200 (* decider4 *)
| NGRAM_CPS_IMPL2_params_3_3_400 (* decider5 *)
| NGRAM_CPS_IMPL1_params_2_2_2_1600. (* decider6 *)