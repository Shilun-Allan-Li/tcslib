# Added source declarations

Base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Head: `fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16`.

69 added source declarations across 8 changed Lean files; 0 removed.
Private source declarations are included. Compiler-generated kernel constants are covered by
the separate stored-constant census and axiom evidence; they are not invented as source commands here.

Reproduce: `python3 -I evidence/tools/new_declarations.py --base eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9 --head fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16 --report evidence/new-declarations-final3.md --json evidence/new-declarations-final3.json`.

The pre-existing target `Authentication.dlHash_crh` has a replaced proof body and is not a new declaration.

## TCSlib/Cryptography/Candidates/DiscreteLog.lean

2 additions.

| Line | Kind | Qualified source name | Visibility |
|---:|---|---|---|
| 486 | theorem | `TCSlib.Cryptography.Candidates.expGenFun_eq` | public |
| 657 | theorem | `TCSlib.Cryptography.Candidates.expSampleRaw_eq` | public |

## TCSlib/Cryptography/Hashing/FromDiscreteLog.lean

21 additions.

| Line | Kind | Qualified source name | Visibility |
|---:|---|---|---|
| 91 | theorem | `TCSlib.Cryptography.Authentication.dlHashIdx_layout` | public |
| 121 | theorem | `TCSlib.Cryptography.Authentication.dlHashGenFun_layout` | public |
| 141 | theorem | `TCSlib.Cryptography.Authentication.dlHashGenFun_key` | public |
| 176 | theorem | `TCSlib.Cryptography.Authentication.dlHashPow_atParam` | public |
| 212 | theorem | `TCSlib.Cryptography.Authentication.dlHashMul_atParam` | public |
| 248 | theorem | `TCSlib.Cryptography.Authentication.dlHashEval_atParam` | public |
| 264 | theorem | `TCSlib.Cryptography.Authentication.dlHashEval_expF` | public |
| 292 | theorem | `TCSlib.Cryptography.Authentication.dlHashEval_collision` | public |
| 324 | theorem | `TCSlib.Cryptography.Authentication.dlHashEval_range` | public |
| 440 | theorem | `TCSlib.Cryptography.Authentication.dlHash_gen_coins` | public |
| 446 | def | `TCSlib.Cryptography.Authentication.dlHash_coinsEquiv` | public |
| 455 | theorem | `TCSlib.Cryptography.Authentication.dlHash_coinsEquiv_eq` | public |
| 463 | theorem | `TCSlib.Cryptography.Authentication.dlHash_coinsEquiv_symm_ofFn` | public |
| 474 | theorem | `TCSlib.Cryptography.Authentication.dlHash_gen_runAt` | public |
| 489 | theorem | `TCSlib.Cryptography.Authentication.dlHash_compresses` | public |
| 524 | def | `TCSlib.Cryptography.Authentication.dlHashCollision` | public |
| 533 | theorem | `TCSlib.Cryptography.Authentication.dlHashCollision_iff` | public |
| 549 | theorem | `TCSlib.Cryptography.Authentication.dlHash_collision_accept_eq` | public |
| 581 | theorem | `TCSlib.Cryptography.Authentication.dlHash_reduction_success` | public |
| 631 | theorem | `TCSlib.Cryptography.Authentication.dlHash_ideal_collision_le` | public |
| 658 | theorem | `TCSlib.Cryptography.Authentication.dlHash_collision_bound` | public |

## TCSlib/Cryptography/Hashing/FromDiscreteLog/Algebra.lean

5 additions.

| Line | Kind | Qualified source name | Visibility |
|---:|---|---|---|
| 40 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.expUnit_pow_val` | public |
| 49 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.residue_difference` | private |
| 59 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.residue_of_unit_pow_mul` | private |
| 76 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.unitCollision_selector_ne` | public |
| 110 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.unitCollision_extract` | public |

## TCSlib/Cryptography/Hashing/FromDiscreteLog/Coins.lean

3 additions.

| Line | Kind | Qualified source name | Visibility |
|---:|---|---|---|
| 39 | def | `TCSlib.Cryptography.Authentication.FromDiscreteLog.sumCoinsEquiv` | public |
| 47 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.sumCoinsEquiv_eq` | public |
| 55 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.sumCoinsEquiv_symm_ofFn` | public |

## TCSlib/Cryptography/Hashing/FromDiscreteLog/Encoding.lean

12 additions.

| Line | Kind | Qualified source name | Visibility |
|---:|---|---|---|
| 43 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.ofFn_splitBits_fst` | public |
| 53 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.ofFn_splitBits_snd` | public |
| 65 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.inputWord_split` | public |
| 70 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.inputWord_take` | public |
| 75 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.inputWord_drop` | public |
| 80 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.inputWord_ext` | public |
| 89 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.inputWord_num_ext` | public |
| 111 | def | `TCSlib.Cryptography.Authentication.FromDiscreteLog.boundedInputEquiv` | public |
| 140 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.boundedInputEquiv_apply` | public |
| 146 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.boundedInputEquiv_symm_apply` | public |
| 152 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.card_boundedInput` | public |
| 164 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.card_boundedRange` | public |

## TCSlib/Cryptography/Hashing/FromDiscreteLog/Probability.lean

2 additions.

| Line | Kind | Qualified source name | Visibility |
|---:|---|---|---|
| 39 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.expect_sample_eq_uexp` | public |
| 50 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collision_accept_eq` | public |

## TCSlib/Cryptography/Hashing/FromDiscreteLog/Reduction.lean

19 additions.

| Line | Kind | Qualified source name | Visibility |
|---:|---|---|---|
| 49 | def | `TCSlib.Cryptography.Authentication.FromDiscreteLog.modularDifference` | public |
| 55 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.modularDifference_eq` | public |
| 62 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.modularDifference_value` | public |
| 71 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.polyTimeComputable_modularDifference` | public |
| 85 | def | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost` | public |
| 98 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_eq` | public |
| 116 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.polyTimeComputable_collisionPost` | public |
| 173 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_ofFn_append` | public |
| 222 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionPost_split` | public |
| 268 | def | `TCSlib.Cryptography.Authentication.FromDiscreteLog.reductionRaw` | public |
| 273 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.reductionRaw_eq` | public |
| 280 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.polyTimeComputable_reductionRaw` | public |
| 290 | def | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionReduction` | public |
| 296 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionReduction_eq` | public |
| 301 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionReduction_coins` | public |
| 306 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionReduction_adv` | public |
| 311 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionReduction_advice` | public |
| 317 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionReduction_runAtL` | public |
| 328 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.collisionReduction_runAt` | public |

## TCSlib/Cryptography/Hashing/FromDiscreteLog/Sampling.lean

5 additions.

| Line | Kind | Qualified source name | Visibility |
|---:|---|---|---|
| 47 | def | `TCSlib.Cryptography.Authentication.FromDiscreteLog.residueFinEquiv` | public |
| 52 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.residueFinEquiv_eq` | public |
| 57 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.residueFinEquiv_val` | public |
| 66 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.expEval_natToList_val` | public |
| 81 | theorem | `TCSlib.Cryptography.Authentication.FromDiscreteLog.sampleBelowL_uprob_le` | public |
