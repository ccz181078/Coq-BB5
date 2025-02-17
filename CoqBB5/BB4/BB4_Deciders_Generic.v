
(**

Enumerative type for the deciders used with generic parameters (i.e. not hardcoded per machine), see BB5_Deciders_Pipeline.v.

Note: this type is isolated because BB5_Enumeration.v and subsequently TNF.v also depend on it in order to report which decider decided which machine.
*)

Inductive DeciderIdentifier : Type :=
| DECIDER_NIL (* Definition HaltDecider_nil:HaltDecider := fun _ => Result_Unknown. *)
| LOOP1_params_107 (* decider2 *)
| NGRAM_CPS_IMPL2_params_1_1_100 (* decider3 *)
| NGRAM_CPS_IMPL2_params_2_2_200 (* decider4 *)
| NGRAM_CPS_IMPL2_params_3_3_400 (* decider5 *)
| NGRAM_CPS_IMPL1_params_2_2_2_1600 (* decider6 *)
| NGRAM_CPS_IMPL1_params_2_3_3_1600 (* decider7 *)
| NGRAM_CPS_IMPL1_params_4_2_2_600 (* decider9 *)
| NGRAM_CPS_IMPL1_params_4_3_3_1600 (* decider10 *)
| NGRAM_CPS_IMPL1_params_6_2_2_3200 (* decider11 *)
| NGRAM_CPS_IMPL1_params_6_3_3_3200 (* decider12 *)
| NGRAM_CPS_IMPL1_params_8_2_2_1600 (* decider13 *)
| NGRAM_CPS_IMPL1_params_8_3_3_1600 (* decider14 *)
| NGRAM_CPS_LRU_params_2_2_10000 (* decider15 *)
| NGRAM_CPS_IMPL1_params_10_4_4_10000 (* decider16 *)
| REPWL_params_4_3_320_10000. (* decider17 *)