
(**

Enumerative type for the deciders used with generic parameters (i.e. not hardcoded per machine), see BB5_Deciders_Pipeline.v.

Note: this type is isolated because BB5_Enumeration.v and subsequently TNF.v also depend on it in order to report which decider decided which machine.
*)

Inductive DeciderIdentifier : Type :=
| DECIDER_NIL (* Definition HaltDecider_nil:HaltDecider := fun _ => Result_Unknown. *)
| LOOP1_params_107 (* decider2 *)
| NGRAM_CPS_IMPL2_params_1_1_400 (* decider3 *)
| NGRAM_CPS_IMPL2_params_2_2_800 (* decider4 *)
| NGRAM_CPS_IMPL2_params_3_3_400 (* decider5 *)
| NGRAM_CPS_IMPL2_params_4_4_800 (* decider6 *)
| LOOP1_params_4100 (* decider7 *)
| REPWL_params_2_3_320_400 (* decider8 *)
| NGRAM_CPS_LRU_params_2_2_1000 (* decider9 *)
| NGRAM_CPS_IMPL1_params_2_2_2_3000 (* decider10 *)
| NGRAM_CPS_IMPL1_params_2_3_3_1600 (* decider11 *)
| NGRAM_CPS_IMPL1_params_4_2_2_600 (* decider12 *)
| NGRAM_CPS_IMPL1_params_4_3_3_1600 (* decider13 *)
| NGRAM_CPS_IMPL1_params_6_2_2_3200 (* decider14 *)
| NGRAM_CPS_IMPL1_params_6_3_3_3200 (* decider15 *)
(* | NGRAM_CPS_IMPL1_params_8_2_2_1600 decider16 *)
| NGRAM_CPS_IMPL1_params_8_3_3_1600 (* decider17 *)
| NGRAM_CPS_LRU_params_3_3_20000 (* decider18 *)
| REPWL_params_4_2_320_2000 (* decider19 *)
| REPWL_params_6_2_320_2000 (* decider20 *) 
| NGRAM_CPS_IMPL2_params_4_4_20000 (* decider21 *)
| HALT_MAX_params_3932964. (* decider22 *)