# Inspection table (final, commit 7d16731e963f60a4ba97e79ec7dba41c86dca1bb)

Every `rw`/`rwa`/`erw`/`nth_rewrite`/`simp`/`simpa`/`simp_all`/`dsimp`/`unfold`/`show`/`change` argument on an added line of `git diff 72fcfbef 7d16731e -- TCSlib/Complexity/SpaceComplexity/Padding.lean`. Kinds resolved by `Probe/EPadKinds.lean` in `namespace Complexity` with `open Turing`.

| line | tactic | argument | kind |
|---:|---|---|---|
| 99 | `rw` | `epadVirt` | own file: def `epadVirt` |
| 99 | `rw` | `if_pos h` | theorem if_pos (Init.Core) |
| 105 | `rw` | `epadVirt` | own file: def `epadVirt` |
| 105 | `rw` | `if_neg h` | theorem if_neg (Init.Core) |
| 111 | `rw` | `epadVirt_of_valid h` | own file: theorem `epadVirt_of_valid` |
| 112 | `rw` | `epadVirt_of_not_valid h` | own file: theorem `epadVirt_of_not_valid` |
| 123 | `rw` | `hd` | local hypothesis / let-bound name |
| 123 | `rw` | `Option.some.injEq` | theorem Option.some.injEq (Init.Core) |
| 123 | `rw` | `Prod.mk.injEq` | theorem Prod.mk.injEq (Init.Core) |
| 133 | `rw` | `hd` | local hypothesis / let-bound name |
| 142 | `show` | `pairEncode y (Nat.bits i) ∈ (epadQ C d mode : Set (List Bool)) ↔ _` | goal restatement |
| 143 | `rw` | `epad_mem_Q_iff (pairDecode_pairEncode y (Nat.bits i))` | own file: theorem `epad_mem_Q_iff` |
| 143 | `rw` | `LogProg.bitsVal_bits` | theorem Complexity.LogProg.bitsVal_bits (TCSlib.Complexity.SpaceComplexity.Machines.Bin) |
| 174 | `rw` | `h` | local hypothesis / let-bound name |
| 175 | `rw` | `h` | local hypothesis / let-bound name |
| 176 | `rw` | `h` | local hypothesis / let-bound name |
| 177 | `rw` | `h` | local hypothesis / let-bound name |
| 178 | `rw` | `h` | local hypothesis / let-bound name |
| 187 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 188 | `simp_all` | `(no lemma list)` | default simp set |
| 218 | `simpa` | `(no lemma list)` | default simp set |
| 222 | `rw` | `← eq` | local hypothesis / let-bound name |
| 222 | `rw` | `Function.update_eq_self` | theorem Function.update_eq_self (Mathlib.Logic.Function.Basic) |
| 222 | `rw` | `List.length_nil` | theorem List.length_nil (Init.Data.List.Basic) |
| 222 | `rw` | `Nat.add_zero` | theorem Nat.add_zero (Init.Core) |
| 222 | `rw` | `Function.update_eq_self` | theorem Function.update_eq_self (Mathlib.Logic.Function.Basic) |
| 223 | `rw` | `e` | local hypothesis / let-bound name |
| 227 | `rwa` | `astep_jeq htest` | local hypothesis / let-bound name |
| 227 | `rwa` | `if_pos eq` | theorem if_pos (Init.Core) |
| 230 | `simp` | `List.length_cons` | theorem List.length_cons (Init.Data.List.Basic) |
| 235 | `simpa` | `(no lemma list)` | default simp set |
| 235 | `simp` | `(no lemma list)` | default simp set |
| 239 | `rw` | `astep_jeq htest` | local hypothesis / let-bound name |
| 239 | `rw` | `if_neg hne` | theorem if_neg (Init.Core) |
| 243 | `rwa` | `astep_call hread` | local hypothesis / let-bound name |
| 243 | `rwa` | `vword_whole₁` | local hypothesis / let-bound name |
| 243 | `rwa` | `hb` | local hypothesis / let-bound name |
| 247 | `simp` | `(no lemma list)` | default simp set |
| 248 | `simp` | `(no lemma list)` | default simp set |
| 255 | `rw` | `hl` | local hypothesis / let-bound name |
| 255 | `rw` | `Nat.mul_succ` | theorem Nat.mul_succ (Init.Data.Nat.Basic) |
| 257 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 257 | `rw` | `Function.update_of_ne hpc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 261 | `rw` | `astep_inc hinc` | local hypothesis / let-bound name |
| 261 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 264 | `show` | `v₁ ptr + stride ≤ B` | goal restatement |
| 265 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 265 | `rw` | `Function.update_of_ne hpc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 266 | `rwa` | `hend` | local hypothesis / let-bound name |
| 266 | `rwa` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 266 | `rwa` | `← hv₂` | local hypothesis / let-bound name |
| 268 | `simp` | `hv₂` | local hypothesis / let-bound name |
| 268 | `simp` | `hv₁` | local hypothesis / let-bound name |
| 268 | `simp` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 268 | `simp` | `Function.update_of_ne hpl.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 268 | `simp` | `Function.update_of_ne hlc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 268 | `simp` | `Function.update_of_ne hpc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 270 | `rw` | `hl` | local hypothesis / let-bound name |
| 270 | `rw` | `Nat.mul_succ` | theorem Nat.mul_succ (Init.Data.Nat.Basic) |
| 272 | `simp` | `hv₂` | local hypothesis / let-bound name |
| 272 | `simp` | `hv₁` | local hypothesis / let-bound name |
| 272 | `simp` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 272 | `simp` | `Function.update_of_ne hpc.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 277 | `simp` | `(no lemma list)` | default simp set |
| 278 | `simp` | `hv₂` | local hypothesis / let-bound name |
| 278 | `simp` | `hv₁` | local hypothesis / let-bound name |
| 278 | `simp` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 278 | `simp` | `Function.update_of_ne hpc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 279 | `simpa` | `Nat.mul_succ` | theorem Nat.mul_succ (Init.Data.Nat.Basic) |
| 279 | `simpa` | `Nat.add_assoc` | theorem Nat.add_assoc (Init.Data.Nat.Basic) |
| 279 | `simpa` | `Nat.add_comm stride` | theorem Nat.add_comm (Init.Data.Nat.Basic) |
| 282 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 285 | `simpa` | `(no lemma list)` | default simp set |
| 285 | `simp` | `(no lemma list)` | default simp set |
| 289 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 289 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 291 | `rwa` | `e` | local hypothesis / let-bound name |
| 293 | `simp` | `(no lemma list)` | default simp set |
| 295 | `simpa` | `(no lemma list)` | default simp set |
| 295 | `simpa` | `(no lemma list)` | default simp set |
| 297 | `rw` | `hfr r hr1 hr2` | local hypothesis / let-bound name |
| 297 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 297 | `rw` | `Function.update_of_ne hr1` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 297 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 297 | `rw` | `Function.update_of_ne hr2` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 319 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 319 | `simp` | `Nat.zero_mul` | theorem Nat.zero_mul (Init.Data.Nat.Basic) |
| 319 | `simp` | `Nat.add_zero` | theorem Nat.add_zero (Init.Core) |
| 320 | `simp_all` | `(no lemma list)` | default simp set |
| 321 | `rw` | `e` | local hypothesis / let-bound name |
| 325 | `rwa` | `astep_jz hml` | local hypothesis / let-bound name |
| 325 | `rwa` | `if_pos hk` | theorem if_pos (Init.Core) |
| 331 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 332 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 332 | `rw` | `Function.update_of_ne hkt.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 332 | `rw` | `ht` | local hypothesis / let-bound name |
| 333 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 333 | `rw` | `Function.update_of_ne hkp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 334 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 334 | `rw` | `Function.update_of_ne hkq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 337 | `rw` | `h₁t` | local hypothesis / let-bound name |
| 339 | `rw` | `← hv₂` | local hypothesis / let-bound name |
| 340 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 347 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 347 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 347 | `rw` | `Function.update_of_ne htq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 347 | `rw` | `h₁p` | local hypothesis / let-bound name |
| 347 | `rw` | `h₁q` | local hypothesis / let-bound name |
| 347 | `rw` | `Nat.one_mul` | theorem Nat.one_mul (Init.Data.Nat.Basic) |
| 351 | `rw` | `← hv₃` | local hypothesis / let-bound name |
| 353 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 355 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 355 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 355 | `rw` | `Function.update_of_ne htq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 355 | `rw` | `h₁p` | local hypothesis / let-bound name |
| 355 | `rw` | `h₁q` | local hypothesis / let-bound name |
| 355 | `rw` | `Nat.one_mul` | theorem Nat.one_mul (Init.Data.Nat.Basic) |
| 359 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 359 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 359 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 360 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 361 | `simp_all` | `(no lemma list)` | default simp set |
| 362 | `rw` | `key` | local hypothesis / let-bound name |
| 362 | `rw` | `key` | local hypothesis / let-bound name |
| 362 | `simp` | `htq` | local hypothesis / let-bound name |
| 362 | `simp` | `hkt.symm` | local hypothesis / let-bound name |
| 362 | `simp` | `ht` | local hypothesis / let-bound name |
| 363 | `rw` | `key` | local hypothesis / let-bound name |
| 363 | `rw` | `key` | local hypothesis / let-bound name |
| 363 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 363 | `simp` | `if_neg hkq.symm` | theorem if_neg (Init.Core) |
| 363 | `simp` | `if_neg hkp.symm` | theorem if_neg (Init.Core) |
| 363 | `simp` | `if_neg hpq` | theorem if_neg (Init.Core) |
| 364 | `rw` | `Nat.succ_mul` | theorem Nat.succ_mul (Init.Data.Nat.Basic) |
| 366 | `rw` | `astep_jz hml` | local hypothesis / let-bound name |
| 366 | `rw` | `if_neg (by omega)` | theorem if_neg (Init.Core) |
| 368 | `rw` | `astep_dec hmd` | local hypothesis / let-bound name |
| 368 | `rw` | `hk` | local hypothesis / let-bound name |
| 368 | `rw` | `Nat.add_sub_cancel` | theorem Nat.add_sub_cancel (Init.Data.Nat.Basic) |
| 368 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 373 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 373 | `simp` | `key` | local hypothesis / let-bound name |
| 374 | `simp_all` | `(no lemma list)` | default simp set |
| 376 | `rwa` | `e` | local hypothesis / let-bound name |
| 404 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 404 | `simp` | `pow_zero` | theorem pow_zero (Mathlib.Algebra.Group.Defs) |
| 404 | `simp` | `Nat.mul_one` | theorem Nat.mul_one (Init.Data.Nat.Basic) |
| 405 | `simp_all` | `(no lemma list)` | default simp set |
| 406 | `rw` | `eq` | local hypothesis / let-bound name |
| 410 | `rwa` | `astep_jz hpw` | local hypothesis / let-bound name |
| 410 | `rwa` | `if_pos he` | theorem if_pos (Init.Core) |
| 421 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 421 | `rw` | `Function.update_of_ne hdk.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 421 | `rw` | `hk` | local hypothesis / let-bound name |
| 427 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 427 | `rw` | `Function.update_of_ne hkt.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 427 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 427 | `rw` | `Function.update_of_ne hdt.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 427 | `rw` | `ht` | local hypothesis / let-bound name |
| 429 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 429 | `rw` | `Function.update_of_ne hkq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 429 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 429 | `rw` | `Function.update_of_ne hkp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 429 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 429 | `rw` | `Function.update_of_ne hdq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 429 | `rw` | `Function.update_of_ne hnd` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 429 | `rw` | `Function.update_of_ne hdp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 429 | `rw` | `hq` | local hypothesis / let-bound name |
| 429 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 429 | `rw` | `Nat.mul_comm` | theorem Nat.mul_comm (Init.Data.Nat.Basic) |
| 435 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 435 | `rw` | `Function.update_of_ne hkq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 435 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 435 | `rw` | `Function.update_of_ne hkp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 435 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 435 | `rw` | `Function.update_of_ne hdq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 435 | `rw` | `Function.update_of_ne hnd` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 435 | `rw` | `Function.update_of_ne hdp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 435 | `rw` | `hq` | local hypothesis / let-bound name |
| 435 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 435 | `rw` | `Nat.mul_comm` | theorem Nat.mul_comm (Init.Data.Nat.Basic) |
| 441 | `rw` | `← hv₃` | local hypothesis / let-bound name |
| 442 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 442 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 442 | `rw` | `hval` | local hypothesis / let-bound name |
| 444 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 446 | `rw` | `hval` | local hypothesis / let-bound name |
| 451 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 451 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 458 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 458 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 458 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 458 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 458 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 458 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 459 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 460 | `simp_all` | `Nat.mul_comm` | theorem Nat.mul_comm (Init.Data.Nat.Basic) |
| 461 | `rw` | `key` | local hypothesis / let-bound name |
| 461 | `rw` | `key` | local hypothesis / let-bound name |
| 461 | `simp` | `hpq.symm` | local hypothesis / let-bound name |
| 461 | `simp` | `hdq.symm` | local hypothesis / let-bound name |
| 461 | `simp` | `hq` | local hypothesis / let-bound name |
| 462 | `rw` | `key` | local hypothesis / let-bound name |
| 462 | `simp` | `hkp` | local hypothesis / let-bound name |
| 462 | `simp` | `hdk.symm` | local hypothesis / let-bound name |
| 462 | `simp` | `hk` | local hypothesis / let-bound name |
| 462 | `rw` | `key` | local hypothesis / let-bound name |
| 462 | `simp` | `htp` | local hypothesis / let-bound name |
| 462 | `simp` | `hdt.symm` | local hypothesis / let-bound name |
| 462 | `simp` | `ht` | local hypothesis / let-bound name |
| 463 | `rw` | `key` | local hypothesis / let-bound name |
| 463 | `simpa` | `hnp` | local hypothesis / let-bound name |
| 463 | `simpa` | `hnd` | local hypothesis / let-bound name |
| 464 | `rw` | `key` | local hypothesis / let-bound name |
| 464 | `rw` | `key` | local hypothesis / let-bound name |
| 464 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 464 | `simp` | `if_neg hdp.symm` | theorem if_neg (Init.Core) |
| 464 | `simp` | `if_neg hnp` | theorem if_neg (Init.Core) |
| 464 | `simp` | `if_neg hnd` | theorem if_neg (Init.Core) |
| 465 | `rw` | `Nat.mul_assoc` | theorem Nat.mul_assoc (Init.Data.Nat.Basic) |
| 465 | `rw` | `← pow_succ'` | theorem pow_succ' (Mathlib.Algebra.Group.Defs) |
| 467 | `rw` | `astep_jz hpw` | local hypothesis / let-bound name |
| 467 | `rw` | `if_neg (by omega)` | theorem if_neg (Init.Core) |
| 469 | `rw` | `astep_dec hpd` | local hypothesis / let-bound name |
| 469 | `rw` | `he` | local hypothesis / let-bound name |
| 469 | `rw` | `Nat.add_sub_cancel` | theorem Nat.add_sub_cancel (Init.Data.Nat.Basic) |
| 469 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 472 | `rw` | `astep_clr hmv` | local hypothesis / let-bound name |
| 472 | `rw` | `← hv₄` | local hypothesis / let-bound name |
| 475 | `rw` | `astep_clr hmvc` | local hypothesis / let-bound name |
| 475 | `rw` | `← hv₆` | local hypothesis / let-bound name |
| 479 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 479 | `simp` | `key` | local hypothesis / let-bound name |
| 480 | `simp_all` | `pow_succ'` | theorem pow_succ' (Mathlib.Algebra.Group.Defs) |
| 480 | `simp_all` | `Nat.mul_assoc` | theorem Nat.mul_assoc (Init.Data.Nat.Basic) |
| 481 | `rwa` | `eq` | local hypothesis / let-bound name |
| 518 | `simp` | `epadVLAll` | own file: def `epadVLAll` |
| 519 | `simp` | `epadVLAll` | own file: def `epadVLAll` |
| 596 | `rw` | `ha'` | local hypothesis / let-bound name |
| 596 | `rw` | `pairDecode_pairEncode` | theorem Turing.pairDecode_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 596 | `rw` | `Option.some.injEq` | theorem Option.some.injEq (Init.Core) |
| 596 | `rw` | `Prod.mk.injEq` | theorem Prod.mk.injEq (Init.Core) |
| 600 | `rw` | `eq_pairEncode_of_pairDecode y a b h` | theorem Turing.eq_pairEncode_of_pairDecode (TCSlib.Complexity.TuringMachine.Encoding) |
| 600 | `rw` | `hb` | local hypothesis / let-bound name |
| 606 | `rw` | `ha` | local hypothesis / let-bound name |
| 606 | `rw` | `pairDecode_pairEncode` | theorem Turing.pairDecode_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 613 | `rw` | `List.eq_replicate_iff` | theorem List.eq_replicate_iff (Init.Data.List.Lemmas) |
| 617 | `rw` | `List.getD_eq_getElem?_getD` | theorem List.getD_eq_getElem?_getD (Init.Data.List.Lemmas) |
| 617 | `rw` | `List.getElem?_eq_getElem hi` | theorem List.getElem?_eq_getElem (Init.GetElem) |
| 617 | `rw` | `Option.getD_some` | theorem Option.getD_some (Init.Data.Option.Basic) |
| 623 | `rwa` | `List.getD_eq_getElem?_getD` | theorem List.getD_eq_getElem?_getD (Init.Data.List.Lemmas) |
| 623 | `rwa` | `List.getElem?_eq_getElem hi` | theorem List.getElem?_eq_getElem (Init.GetElem) |
| 623 | `rwa` | `Option.getD_some` | theorem Option.getD_some (Init.Data.Option.Basic) |
| 645 | `rw` | `← hs_def` | local hypothesis / let-bound name |
| 646 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 646 | `rw` | `epadS` | own file: def `epadS` |
| 647 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 647 | `rw` | `epadS` | own file: def `epadS` |
| 650 | `rw` | `h` | local hypothesis / let-bound name |
| 657 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 657 | `simp` | `epadS` | own file: def `epadS` |
| 661 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 661 | `simp` | `epadS` | own file: def `epadS` |
| 661 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 667 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 671 | `rw` | `h0` | local hypothesis / let-bound name |
| 671 | `rw` | `h1` | local hypothesis / let-bound name |
| 671 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 671 | `rw` | `h0` | local hypothesis / let-bound name |
| 671 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 674 | `simp` | `hd` | local hypothesis / let-bound name |
| 680 | `rw` | `h0` | local hypothesis / let-bound name |
| 680 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 682 | `rw` | `if_neg hnv` | theorem if_neg (Init.Core) |
| 685 | `simp` | `hd` | local hypothesis / let-bound name |
| 687 | `rw` | `hy'` | local hypothesis / let-bound name |
| 687 | `rw` | `length_pairEncode` | theorem Turing.length_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 688 | `rw` | `hy'` | local hypothesis / let-bound name |
| 688 | `rw` | `pairFstD_pairEncode` | theorem Complexity.pairFstD_pairEncode (TCSlib.Complexity.ClassNP.PolyTimePairing) |
| 698 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 701 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 701 | `rw` | `h0` | local hypothesis / let-bound name |
| 705 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 705 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 705 | `rw` | `hz 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 708 | `rw` | `← hv₂` | local hypothesis / let-bound name |
| 709 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 712 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 714 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 714 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 714 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 714 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 714 | `rw` | `h0` | local hypothesis / let-bound name |
| 714 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 719 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 722 | `rw` | `astep_half hc` | local hypothesis / let-bound name |
| 722 | `rw` | `h₂₂` | local hypothesis / let-bound name |
| 722 | `rw` | `hs` | local hypothesis / let-bound name |
| 722 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 724 | `rw` | `this` | local hypothesis / let-bound name |
| 727 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 731 | `rw` | `astep_half hc` | local hypothesis / let-bound name |
| 731 | `rw` | `h₂₂` | local hypothesis / let-bound name |
| 731 | `rw` | `hs` | local hypothesis / let-bound name |
| 734 | `rw` | `astep_half hc'` | local hypothesis / let-bound name |
| 734 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 734 | `rw` | `Function.update_idem` | theorem Function.update_idem (Mathlib.Logic.Function.Basic) |
| 734 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 736 | `rw` | `this` | local hypothesis / let-bound name |
| 740 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 740 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 740 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 740 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 740 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 740 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 740 | `rw` | `h0` | local hypothesis / let-bound name |
| 740 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 743 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 743 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 743 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 743 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 743 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 743 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 743 | `rw` | `h1` | local hypothesis / let-bound name |
| 747 | `rw` | `h` | local hypothesis / let-bound name |
| 747 | `simp` | `(no lemma list)` | default simp set |
| 748 | `rw` | `h` | local hypothesis / let-bound name |
| 748 | `simp` | `(no lemma list)` | default simp set |
| 749 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 749 | `rw` | `Function.update_of_ne h2` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 749 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 749 | `rw` | `Function.update_of_ne h2` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 749 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 749 | `rw` | `Function.update_of_ne h0'` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 755 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 755 | `simp` | `epadS` | own file: def `epadS` |
| 759 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 759 | `simp` | `epadS` | own file: def `epadS` |
| 759 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 763 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 767 | `rw` | `hv₃0` | local hypothesis / let-bound name |
| 767 | `rw` | `hv₃1` | local hypothesis / let-bound name |
| 767 | `rw` | `hlen` | local hypothesis / let-bound name |
| 767 | `rw` | `Nat.mul_add` | theorem Nat.mul_add (Init.Data.Nat.Basic) |
| 768 | `rw` | `hv₃r 3 (by decide)` | local hypothesis / let-bound name |
| 768 | `rw` | `hz 3 (by decide) (by decide)` | local hypothesis / let-bound name |
| 771 | `rw` | `hy'` | local hypothesis / let-bound name |
| 771 | `rw` | `pairEncode_getD_snd` | theorem Complexity.pairEncode_getD_snd (TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess) |
| 772 | `rw` | `hv₃0` | local hypothesis / let-bound name |
| 772 | `rw` | `← h` | local hypothesis / let-bound name |
| 772 | `rw` | `← Nat.mul_add` | theorem Nat.mul_add (Init.Data.Nat.Basic) |
| 778 | `rw` | `← hv₄` | local hypothesis / let-bound name |
| 780 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 782 | `rw` | `hv₃r 3 (by decide)` | local hypothesis / let-bound name |
| 782 | `rw` | `hz 3 (by decide) (by decide)` | local hypothesis / let-bound name |
| 785 | `rw` | `h` | local hypothesis / let-bound name |
| 785 | `simp` | `(no lemma list)` | default simp set |
| 786 | `rw` | `h` | local hypothesis / let-bound name |
| 786 | `simp` | `(no lemma list)` | default simp set |
| 787 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 787 | `rw` | `Function.update_of_ne h3` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 787 | `rw` | `Function.update_of_ne h0'` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 787 | `rw` | `hv₃r r (by omega)` | local hypothesis / let-bound name |
| 789 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 789 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 789 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 789 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 789 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 792 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 792 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 792 | `rw` | `hv₃r 3 (by decide)` | local hypothesis / let-bound name |
| 792 | `rw` | `hz 3 (by decide) (by decide)` | local hypothesis / let-bound name |
| 792 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 796 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 798 | `rw` | `e1` | local hypothesis / let-bound name |
| 800 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 800 | `rw` | `hv₄r 4 (by decide)` | local hypothesis / let-bound name |
| 800 | `rw` | `hz 4 (by decide) (by decide)` | local hypothesis / let-bound name |
| 802 | `rw` | `eC` | local hypothesis / let-bound name |
| 802 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 802 | `rw` | `hv₄r 4 (by decide)` | local hypothesis / let-bound name |
| 802 | `rw` | `hz 4 (by decide) (by decide)` | local hypothesis / let-bound name |
| 802 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 804 | `rw` | `← hv₅` | local hypothesis / let-bound name |
| 806 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 809 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 811 | `rw` | `e1` | local hypothesis / let-bound name |
| 813 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 813 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 813 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 813 | `rw` | `hv₄r 8 (by decide)` | local hypothesis / let-bound name |
| 813 | `rw` | `hz 8 (by decide) (by decide)` | local hypothesis / let-bound name |
| 817 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 817 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 817 | `rw` | `hv₄r 8 (by decide)` | local hypothesis / let-bound name |
| 817 | `rw` | `hz 8 (by decide) (by decide)` | local hypothesis / let-bound name |
| 819 | `rw` | `eD` | local hypothesis / let-bound name |
| 819 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 819 | `rw` | `hv₅8` | local hypothesis / let-bound name |
| 819 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 821 | `rw` | `← hv₆` | local hypothesis / let-bound name |
| 823 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 826 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 826 | `rw` | `Function.update_of_ne h8` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 826 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 826 | `rw` | `Function.update_of_ne h4` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 835 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 835 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 836 | `rw` | `hv₆r 5 (by decide) (by decide)` | local hypothesis / let-bound name |
| 836 | `rw` | `hv₄r 5 (by decide)` | local hypothesis / let-bound name |
| 836 | `rw` | `hz 5 (by decide) (by decide)` | local hypothesis / let-bound name |
| 837 | `rw` | `hv₆r 6 (by decide) (by decide)` | local hypothesis / let-bound name |
| 837 | `rw` | `hv₄r 6 (by decide)` | local hypothesis / let-bound name |
| 837 | `rw` | `hz 6 (by decide) (by decide)` | local hypothesis / let-bound name |
| 838 | `rw` | `hv₆r 7 (by decide) (by decide)` | local hypothesis / let-bound name |
| 838 | `rw` | `hv₄r 7 (by decide)` | local hypothesis / let-bound name |
| 838 | `rw` | `hz 7 (by decide) (by decide)` | local hypothesis / let-bound name |
| 839 | `rw` | `hv₆r 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 839 | `rw` | `hv₄2` | local hypothesis / let-bound name |
| 840 | `rw` | `hv₆r 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 840 | `rw` | `hv₄2` | local hypothesis / let-bound name |
| 840 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 840 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 840 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 840 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 843 | `rw` | `hv₆r 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 843 | `rw` | `hv₄2` | local hypothesis / let-bound name |
| 843 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 843 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 843 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 843 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 845 | `rw` | `hp6` | local hypothesis / let-bound name |
| 848 | `rw` | `← hv₇` | local hypothesis / let-bound name |
| 850 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 854 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 854 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 854 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 854 | `rw` | `hv₆r 3 (by decide) (by decide)` | local hypothesis / let-bound name |
| 854 | `rw` | `hv₄3` | local hypothesis / let-bound name |
| 856 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 856 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 858 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 858 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 858 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 858 | `rw` | `hv₆r 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 858 | `rw` | `hv₄2` | local hypothesis / let-bound name |
| 864 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 864 | `rw` | `Function.update_of_ne h4` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 864 | `rw` | `Function.update_of_ne h8` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 864 | `rw` | `hv₆r r h4 h8` | local hypothesis / let-bound name |
| 864 | `rw` | `hv₄r r (by omega)` | local hypothesis / let-bound name |
| 867 | `rw` | `hval` | local hypothesis / let-bound name |
| 867 | `rw` | `epad_eq_replicate_iff` | own file: theorem `epad_eq_replicate_iff` |
| 870 | `rw` | `hv₇2` | local hypothesis / let-bound name |
| 870 | `rw` | `hfst` | local hypothesis / let-bound name |
| 875 | `show` | `(3 : Fin 18) ≠ 4` | goal restatement |
| 876 | `rw` | `astep_jeq hcmp` | local hypothesis / let-bound name |
| 876 | `rw` | `hv₇3` | local hypothesis / let-bound name |
| 876 | `rw` | `hv₇4` | local hypothesis / let-bound name |
| 878 | `rw` | `if_pos (hiff.mp hv')` | theorem if_pos (Init.Core) |
| 879 | `rwa` | `if_pos hv'` | theorem if_pos (Init.Core) |
| 880 | `rw` | `if_neg (fun h => hv' (hiff.mpr h))` | theorem if_neg (Init.Core) |
| 881 | `rwa` | `if_neg hv'` | theorem if_neg (Init.Core) |
| 886 | `simpa` | `(no lemma list)` | default simp set |
| 891 | `rw` | `hfr r (hfar r hr9 0 (by decide)) (hfar r hr9 3 (by decide))` | local hypothesis / let-bound name |
| 891 | `rw` | `hv₃r r (by omega)` | local hypothesis / let-bound name |
| 892 | `rw` | `if_neg hnv` | theorem if_neg (Init.Core) |
| 904 | `simp` | `(no lemma list)` | default simp set |
| 921 | `show` | `inputBitLang ∈ LOGSPACE` | goal restatement |
| 923 | `show` | `inputLenLang ∈ LOGSPACE` | goal restatement |
| 935 | `show` | `MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _ ∧` | goal restatement |
| 972 | `rw` | `show epadS false * j = j from Nat.one_mul j` | term (an inline `show … from …` equation) |
| 972 | `show` | `epadS false * j = j` | goal restatement |
| 976 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 977 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 979 | `rw` | `Function.update_of_ne (fun h => by rw [h] at h2; simp at h2)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 979 | `rw` | `h` | local hypothesis / let-bound name |
| 979 | `simp` | `(no lemma list)` | default simp set |
| 983 | `rw` | `indicator_eq_decide` | local hypothesis / let-bound name |
| 984 | `rw` | `if_pos hv` | theorem if_pos (Init.Core) |
| 984 | `rw` | `hy` | local hypothesis / let-bound name |
| 985 | `show` | `epadVA C d (.inr .yes) = .ret true` | goal restatement |
| 987 | `rw` | `indicator_eq_decide` | local hypothesis / let-bound name |
| 988 | `rw` | `if_neg hv` | theorem if_neg (Init.Core) |
| 988 | `rw` | `hy` | local hypothesis / let-bound name |
| 989 | `show` | `epadVA C d (.inr .no) = .ret false` | goal restatement |
| 1031 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1032 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1033 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1034 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1035 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1036 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1037 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1038 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1039 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1040 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1041 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1042 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1043 | `simp` | `epadBXAll` | own file: def `epadBXAll` |
| 1116 | `rw` | `h17` | local hypothesis / let-bound name |
| 1118 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 1119 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1121 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1127 | `rw` | `astep_dec hc` | local hypothesis / let-bound name |
| 1127 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1127 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1127 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 1127 | `rw` | `h2` | local hypothesis / let-bound name |
| 1127 | `rw` | `Nat.add_sub_cancel` | theorem Nat.add_sub_cancel (Init.Data.Nat.Basic) |
| 1127 | `rw` | `Function.update_idem` | theorem Function.update_idem (Mathlib.Logic.Function.Basic) |
| 1136 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1136 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 1136 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1136 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1136 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1136 | `rw` | `h16` | local hypothesis / let-bound name |
| 1141 | `rw` | `← hv₃` | local hypothesis / let-bound name |
| 1144 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 1144 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1144 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1145 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 1145 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1145 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1145 | `simp` | `h16` | local hypothesis / let-bound name |
| 1146 | `simp_all` | `(no lemma list)` | default simp set |
| 1148 | `rw` | `h₃` | local hypothesis / let-bound name |
| 1159 | `rw` | `h₃` | local hypothesis / let-bound name |
| 1159 | `rw` | `h₃` | local hypothesis / let-bound name |
| 1159 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1159 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1159 | `simp` | `h15` | local hypothesis / let-bound name |
| 1160 | `rw` | `h₃` | local hypothesis / let-bound name |
| 1160 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1160 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1161 | `rw` | `h₃` | local hypothesis / let-bound name |
| 1161 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1161 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1162 | `rw` | `h₃` | local hypothesis / let-bound name |
| 1162 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1162 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1162 | `simp` | `h13` | local hypothesis / let-bound name |
| 1163 | `rw` | `h₃` | local hypothesis / let-bound name |
| 1163 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1163 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1164 | `rw` | `h₃` | local hypothesis / let-bound name |
| 1164 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1164 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1164 | `simp` | `h15` | local hypothesis / let-bound name |
| 1165 | `rw` | `h313` | local hypothesis / let-bound name |
| 1165 | `rw` | `h317` | local hypothesis / let-bound name |
| 1165 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 1168 | `rw` | `if_pos hi` | theorem if_pos (Init.Core) |
| 1171 | `rw` | `← hv₄` | local hypothesis / let-bound name |
| 1173 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 1175 | `rw` | `h315` | local hypothesis / let-bound name |
| 1177 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 1177 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1177 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 1177 | `rw` | `h315` | local hypothesis / let-bound name |
| 1181 | `show` | `epadBA C d false (.inr .hit) = .ret true` | goal restatement |
| 1186 | `rw` | `astep_call hc` | local hypothesis / let-bound name |
| 1186 | `rw` | `vword_whole₁` | local hypothesis / let-bound name |
| 1186 | `rw` | `h415` | local hypothesis / let-bound name |
| 1189 | `rw` | `ho` | local hypothesis / let-bound name |
| 1191 | `show` | `epadBA C d true (.inr .no) = .ret false` | goal restatement |
| 1193 | `show` | `epadBA C d true (.inr .yes) = .ret true` | goal restatement |
| 1195 | `rw` | `if_neg hi` | theorem if_neg (Init.Core) |
| 1198 | `rw` | `← hv₄` | local hypothesis / let-bound name |
| 1200 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 1203 | `show` | `epadBA C d mode (.inr .no) = .ret false` | goal restatement |
| 1208 | `simp` | `Nat.zero_bits` | theorem Nat.zero_bits (Mathlib.Data.Nat.Bits) |
| 1212 | `rw` | `pow_succ` | theorem pow_succ (Mathlib.Algebra.Group.Defs) |
| 1247 | `rw` | `← hv₀` | local hypothesis / let-bound name |
| 1249 | `rw` | `hv₀` | local hypothesis / let-bound name |
| 1251 | `rw` | `hv₀` | local hypothesis / let-bound name |
| 1251 | `rw` | `Function.update_of_ne hr` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1252 | `rw` | `hv₀` | local hypothesis / let-bound name |
| 1252 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 1260 | `rw` | `h₀9` | local hypothesis / let-bound name |
| 1260 | `rw` | `h₀ 10 (by decide)` | local hypothesis / let-bound name |
| 1261 | `rw` | `h₀ 10 (by decide)` | local hypothesis / let-bound name |
| 1261 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 1261 | `rw` | `Nat.one_mul` | theorem Nat.one_mul (Init.Data.Nat.Basic) |
| 1264 | `simp` | `hd` | local hypothesis / let-bound name |
| 1266 | `rw` | `h₀ 10 (by decide)` | local hypothesis / let-bound name |
| 1267 | `simp` | `hd` | local hypothesis / let-bound name |
| 1269 | `rw` | `hz` | local hypothesis / let-bound name |
| 1269 | `rw` | `length_pairEncode` | theorem Turing.length_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 1272 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 1274 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1274 | `rw` | `h₀ 10 (by decide)` | local hypothesis / let-bound name |
| 1276 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1276 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 1276 | `rw` | `h₀ 10 (by decide)` | local hypothesis / let-bound name |
| 1280 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1280 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1280 | `rw` | `h₀ 11 (by decide)` | local hypothesis / let-bound name |
| 1282 | `rw` | `← hv₂` | local hypothesis / let-bound name |
| 1283 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1286 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1286 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1286 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1286 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1286 | `rw` | `h₀ 1 (by decide)` | local hypothesis / let-bound name |
| 1290 | `rw` | `← hv₃` | local hypothesis / let-bound name |
| 1291 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 1293 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1293 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1293 | `rw` | `h₁10` | local hypothesis / let-bound name |
| 1295 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 1302 | `rw` | `astep_dec hc` | local hypothesis / let-bound name |
| 1305 | `rw` | `astep_dec hc'` | local hypothesis / let-bound name |
| 1308 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 1308 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 1310 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 1311 | `simp_all` | `(no lemma list)` | default simp set |
| 1312 | `rw` | `e` | local hypothesis / let-bound name |
| 1316 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 1316 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1316 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 1316 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1316 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1316 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1316 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1316 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1316 | `rw` | `h₀ 12 (by decide)` | local hypothesis / let-bound name |
| 1321 | `rw` | `← hv₅` | local hypothesis / let-bound name |
| 1322 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 1324 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 1330 | `rw` | `astep_half hc` | local hypothesis / let-bound name |
| 1332 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 1332 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 1334 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 1335 | `simp_all` | `(no lemma list)` | default simp set |
| 1336 | `rw` | `e` | local hypothesis / let-bound name |
| 1343 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 1343 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 1343 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 1343 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 1343 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 1343 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 1343 | `rw` | `hv₀` | local hypothesis / let-bound name |
| 1344 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 1344 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1344 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1345 | `simp_all` | `(no lemma list)` | default simp set |
| 1353 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1353 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1353 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1353 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1355 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1355 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1355 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1355 | `simp` | `Nat.one_mul` | theorem Nat.one_mul (Init.Data.Nat.Basic) |
| 1356 | `rw` | `(epadIn_answer z _).1` | term |
| 1356 | `rw` | `hz` | local hypothesis / let-bound name |
| 1356 | `rw` | `pairEncode_getD_snd` | theorem Complexity.pairEncode_getD_snd (TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess) |
| 1358 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1358 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1358 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1359 | `rw` | `h612` | local hypothesis / let-bound name |
| 1368 | `rw` | `hno` | local hypothesis / let-bound name |
| 1371 | `rw` | `if_pos hok.2` | theorem if_pos (Init.Core) |
| 1371 | `rw` | `if_pos hok.1` | theorem if_pos (Init.Core) |
| 1374 | `rw` | `hfr' 9 (by decide) (by decide)` | local hypothesis / let-bound name |
| 1374 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1374 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1374 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1377 | `rw` | `h'9` | local hypothesis / let-bound name |
| 1377 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1377 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1377 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1379 | `rw` | `← hv₇` | local hypothesis / let-bound name |
| 1380 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 1382 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 1382 | `rw` | `Function.update_of_ne h10` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1382 | `rw` | `hfr' r h10 h12` | local hypothesis / let-bound name |
| 1388 | `simp` | `(no lemma list)` | default simp set |
| 1403 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 1403 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 1403 | `rw` | `h'9` | local hypothesis / let-bound name |
| 1403 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 1403 | `rw` | `hfr' 11 (by decide) (by decide)` | local hypothesis / let-bound name |
| 1403 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1405 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1405 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1406 | `rw` | `h₇ 13 (by decide) (by decide)` | local hypothesis / let-bound name |
| 1406 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1406 | `rw` | `List.drop_length` | theorem List.drop_length (Init.Data.List.TakeDrop) |
| 1407 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1407 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1408 | `rw` | `← Nat.zero_bits` | theorem Nat.zero_bits (Mathlib.Data.Nat.Bits) |
| 1408 | `rw` | `LogProg.bitsVal_bits` | theorem Complexity.LogProg.bitsVal_bits (TCSlib.Complexity.SpaceComplexity.Machines.Bin) |
| 1409 | `rw` | `h₇ 14 (by decide) (by decide)` | local hypothesis / let-bound name |
| 1409 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1409 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1409 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1411 | `rw` | `h₇ 11 (by decide) (by decide)` | local hypothesis / let-bound name |
| 1411 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1411 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1411 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1412 | `rw` | `(epadIn_answer z _).1` | term |
| 1412 | `rw` | `hz` | local hypothesis / let-bound name |
| 1412 | `rw` | `pairEncode_getD_snd` | theorem Complexity.pairEncode_getD_snd (TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess) |
| 1415 | `rw` | `hfr'' r h10 h13 h14` | local hypothesis / let-bound name |
| 1415 | `rw` | `h₇ r h10 h12` | local hypothesis / let-bound name |
| 1418 | `rw` | `h'' 0 (by decide) (by decide) (by decide) (by decide)` | local hypothesis / let-bound name |
| 1418 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1419 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1419 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1420 | `rw` | `h'' 1 (by decide) (by decide) (by decide) (by decide)` | local hypothesis / let-bound name |
| 1420 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1421 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1422 | `rw` | `h` | local hypothesis / let-bound name |
| 1423 | `rw` | `h` | local hypothesis / let-bound name |
| 1423 | `simp` | `(no lemma list)` | default simp set |
| 1424 | `rw` | `h'' r (hne 10 (by decide)) (hne 12 (by decide)) (hne 13 (by decide))       (hne 14 (by decide))` | local hypothesis / let-bound name |
| 1424 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1424 | `rw` | `if_neg hne1` | theorem if_neg (Init.Core) |
| 1424 | `rw` | `if_neg (hne 9 (by decide))` | theorem if_neg (Init.Core) |
| 1424 | `rw` | `if_neg (hne 10 (by decide))` | theorem if_neg (Init.Core) |
| 1424 | `rw` | `if_neg (hne 11 (by decide))` | theorem if_neg (Init.Core) |
| 1424 | `rw` | `if_neg (hne 12 (by decide))` | theorem if_neg (Init.Core) |
| 1427 | `rw` | `h'' 15 (by decide) (by decide) (by decide) (by decide)` | local hypothesis / let-bound name |
| 1427 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1428 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1428 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1429 | `rw` | `h'' 16 (by decide) (by decide) (by decide) (by decide)` | local hypothesis / let-bound name |
| 1429 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1430 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1430 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1431 | `rw` | `h'' 17 (by decide) (by decide) (by decide) (by decide)` | local hypothesis / let-bound name |
| 1431 | `rw` | `h₆` | local hypothesis / let-bound name |
| 1432 | `simp` | `Fin.reduceEq` | simproc Fin.reduceEq (Lean core) |
| 1432 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 1437 | `rw` | `pairEncode_getD` | theorem Complexity.pairEncode_getD (TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess) |
| 1437 | `rw` | `if_pos (by rw [length_pairEncode]; omega)` | theorem if_pos (Init.Core) |
| 1437 | `rw` | `show 4 * i / 2 = 2 * i by omega` | term (an inline `show … from …` equation) |
| 1437 | `rw` | `pairEncode_getD` | theorem Complexity.pairEncode_getD (TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess) |
| 1437 | `rw` | `if_pos (by omega)` | theorem if_pos (Init.Core) |
| 1437 | `rw` | `show 2 * i / 2 = i by omega` | term (an inline `show … from …` equation) |
| 1437 | `rw` | `length_pairEncode` | theorem Turing.length_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 1438 | `show` | `4 * i / 2 = 2 * i` | goal restatement |
| 1439 | `show` | `2 * i / 2 = i` | goal restatement |
| 1460 | `show` | `epadBA C d mode (.inr .no) = .ret false` | goal restatement |
| 1465 | `rw` | `indicator_eq_decide` | local hypothesis / let-bound name |
| 1466 | `rw` | `hans` | local hypothesis / let-bound name |
| 1472 | `rw` | `hz` | local hypothesis / let-bound name |
| 1472 | `rw` | `length_pairEncode` | theorem Turing.length_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 1480 | `rw` | `show epadS true * j = 2 * j from rfl` | term (an inline `show … from …` equation) |
| 1480 | `rw` | `(epadIn_answer z _).1` | term |
| 1480 | `rw` | `hz` | local hypothesis / let-bound name |
| 1480 | `rw` | `pairEncode_getD` | theorem Complexity.pairEncode_getD (TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess) |
| 1480 | `rw` | `if_pos (by omega)` | theorem if_pos (Init.Core) |
| 1480 | `rw` | `show 2 * j / 2 = j by omega` | term (an inline `show … from …` equation) |
| 1480 | `show` | `epadS true * j = 2 * j` | goal restatement |
| 1481 | `show` | `2 * j / 2 = j` | goal restatement |
| 1484 | `rw` | `if_pos hvy` | theorem if_pos (Init.Core) |
| 1486 | `rw` | `ha` | local hypothesis / let-bound name |
| 1486 | `rw` | `pairFstD_pairEncode` | theorem Complexity.pairFstD_pairEncode (TCSlib.Complexity.ClassNP.PolyTimePairing) |
| 1488 | `rw` | `ha` | local hypothesis / let-bound name |
| 1488 | `rw` | `length_pairEncode` | theorem Turing.length_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 1488 | `rw` | `List.length_replicate` | theorem List.length_replicate (Init.Data.List.Basic) |
| 1490 | `rw` | `hval2 ⟨a, ha⟩` | local hypothesis / let-bound name |
| 1490 | `rw` | `hfst` | local hypothesis / let-bound name |
| 1491 | `rw` | `hfr 13 (by decide)` | local hypothesis / let-bound name |
| 1491 | `rw` | `h13` | local hypothesis / let-bound name |
| 1491 | `rw` | `hfr 15 (by decide)` | local hypothesis / let-bound name |
| 1491 | `rw` | `h15` | local hypothesis / let-bound name |
| 1492 | `rw` | `hfr 16 (by decide)` | local hypothesis / let-bound name |
| 1492 | `rw` | `h16` | local hypothesis / let-bound name |
| 1492 | `rw` | `hfr 17 (by decide)` | local hypothesis / let-bound name |
| 1492 | `rw` | `h17` | local hypothesis / let-bound name |
| 1496 | `rw` | `indicator_eq_decide` | local hypothesis / let-bound name |
| 1498 | `rw` | `hfst` | local hypothesis / let-bound name |
| 1500 | `rw` | `if_pos hi` | theorem if_pos (Init.Core) |
| 1503 | `simpa` | `(no lemma list)` | default simp set |
| 1506 | `rw` | `hz` | local hypothesis / let-bound name |
| 1506 | `rw` | `ha` | local hypothesis / let-bound name |
| 1506 | `rw` | `epad_getD_four a _ w _ hi` | own file: theorem `epad_getD_four` |
| 1507 | `rw` | `if_pos rfl` | theorem if_pos (Init.Core) |
| 1507 | `rw` | `h4` | local hypothesis / let-bound name |
| 1511 | `rw` | `if_pos rfl` | theorem if_pos (Init.Core) |
| 1511 | `rw` | `hb` | local hypothesis / let-bound name |
| 1513 | `rw` | `if_pos rfl` | theorem if_pos (Init.Core) |
| 1514 | `rw` | `if_neg hi` | theorem if_neg (Init.Core) |
| 1518 | `simpa` | `(no lemma list)` | default simp set |
| 1520 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 1521 | `rw` | `List.getD_eq_default _ _ (by omega)` | theorem List.getD_eq_default (Mathlib.Data.List.GetD) |
| 1523 | `rw` | `hans` | local hypothesis / let-bound name |
| 1525 | `rw` | `if_neg hvy` | theorem if_neg (Init.Core) |
| 1527 | `rw` | `indicator_eq_decide` | local hypothesis / let-bound name |
| 1529 | `rw` | `hans` | local hypothesis / let-bound name |
| 1533 | `rw` | `indicator_eq_decide` | local hypothesis / let-bound name |
| 1536 | `rw` | `hans` | local hypothesis / let-bound name |
| 1559 | `rw` | `LOGSPACE_eq` | theorem Complexity.LOGSPACE_eq (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1559 | `rw` | `mem_SPACE_iff` | theorem Complexity.mem_SPACE_iff (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1568 | `show` | `M0.DecidesInSpace (epadQ C d false) (fun n => c0 * logSpace n)` | goal restatement |
| 1570 | `show` | `M1.DecidesInSpace (epadQ C d true) (fun n => c1 * logSpace n)` | goal restatement |
| 1575 | `show` | `c0 * logSpace q ≤ (c0 + c1) * (q + 1)` | goal restatement |
| 1577 | `show` | `c1 * logSpace q ≤ (c0 + c1) * (q + 1)` | goal restatement |
| 1583 | `rw` | `FinTM.computesInSpace_iff` | theorem Turing.FinTM.computesInSpace_iff (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1599 | `rw` | `length_pairEncode` | theorem Turing.length_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 1609 | `show` | `pairEncode y (Nat.bits i) ∈ epadQ C d false ↔ i < v.length` | goal restatement |
| 1610 | `rw` | `epad_query_mem_iff C d false y i (hi.trans hvm)` | own file: theorem `epad_query_mem_iff` |
| 1611 | `simp` | `Bool.false_eq_true` | theorem Bool.false_eq_true (Init.Data.Bool) |
| 1611 | `simp` | `if_false` | theorem if_false (Init.ByCases) |
| 1613 | `rw` | `hv` | local hypothesis / let-bound name |
| 1613 | `rw` | `epadVirt_of_valid hval` | own file: theorem `epadVirt_of_valid` |
| 1615 | `rw` | `hv` | local hypothesis / let-bound name |
| 1615 | `rw` | `epadVirt_of_not_valid hval` | own file: theorem `epadVirt_of_not_valid` |
| 1620 | `show` | `pairEncode y (Nat.bits i) ∈ epadQ C d true ↔ v.getD i false = true` | goal restatement |
| 1621 | `rw` | `epad_query_mem_iff C d true y i (hi.le.trans hvm)` | own file: theorem `epad_query_mem_iff` |
| 1622 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 1624 | `rw` | `hv` | local hypothesis / let-bound name |
| 1624 | `rw` | `epadVirt_of_valid hval` | own file: theorem `epadVirt_of_valid` |
| 1626 | `rw` | `hv` | local hypothesis / let-bound name |
| 1626 | `rw` | `epadVirt_of_not_valid hval` | own file: theorem `epadVirt_of_not_valid` |
| 1637 | `rw` | `hv` | local hypothesis / let-bound name |
| 1637 | `rw` | `epadVirt_of_valid ⟨a, ha⟩` | own file: theorem `epadVirt_of_valid` |
| 1637 | `rw` | `ha` | local hypothesis / let-bound name |
| 1637 | `rw` | `pairFstD_pairEncode` | theorem Complexity.pairFstD_pairEncode (TCSlib.Complexity.ClassNP.PolyTimePairing) |
| 1639 | `rw` | `ha` | local hypothesis / let-bound name |
| 1639 | `rw` | `length_pairEncode` | theorem Turing.length_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 1639 | `rw` | `List.length_replicate` | theorem List.length_replicate (Init.Data.List.Basic) |
| 1640 | `rw` | `hva` | local hypothesis / let-bound name |
| 1642 | `rw` | `← hma` | local hypothesis / let-bound name |
| 1645 | `rw` | `hv` | local hypothesis / let-bound name |
| 1645 | `rw` | `epadVirt_of_not_valid hval` | own file: theorem `epadVirt_of_not_valid` |
| 1646 | `rw` | `hv0` | local hypothesis / let-bound name |
| 1660 | `rw` | `e` | local hypothesis / let-bound name |
| 1660 | `rw` | `hB` | local hypothesis / let-bound name |
| 1667 | `rw` | `e` | local hypothesis / let-bound name |
| 1675 | `rw` | `e` | local hypothesis / let-bound name |
| 1708 | `rw` | `LOGSPACE_eq` | theorem Complexity.LOGSPACE_eq (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1708 | `rw` | `mem_SPACE_iff` | theorem Complexity.mem_SPACE_iff (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1710 | `rw` | `FinTM.decidesInSpace_iff` | theorem Turing.FinTM.decidesInSpace_iff (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1717 | `rw` | `mem_SPACE_iff` | theorem Complexity.mem_SPACE_iff (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1719 | `rw` | `FinTM.decidesInSpace_iff` | theorem Turing.FinTM.decidesInSpace_iff (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1719 | `rw` | `FinTM.computesInSpace_iff` | theorem Turing.FinTM.computesInSpace_iff (TCSlib.Complexity.SpaceComplexity.Basic) |
| 1724 | `rw` | `LogProg.indicator_eq_decide` | theorem Complexity.LogProg.indicator_eq_decide (TCSlib.Complexity.SpaceComplexity.Machines.ARMKit) |
| 1724 | `rw` | `LogProg.indicator_eq_decide` | theorem Complexity.LogProg.indicator_eq_decide (TCSlib.Complexity.SpaceComplexity.Machines.ARMKit) |
| 1724 | `rw` | `LogProg.indicator_eq_decide` | theorem Complexity.LogProg.indicator_eq_decide (TCSlib.Complexity.SpaceComplexity.Machines.ARMKit) |
| 1727 | `rw` | `epadVirt_of_valid hval` | own file: theorem `epadVirt_of_valid` |
| 1731 | `rw` | `ha` | local hypothesis / let-bound name |
| 1731 | `rw` | `pairFstD_pairEncode` | theorem Complexity.pairFstD_pairEncode (TCSlib.Complexity.ClassNP.PolyTimePairing) |
| 1736 | `rw` | `pairFstD_pairEncode` | theorem Complexity.pairFstD_pairEncode (TCSlib.Complexity.ClassNP.PolyTimePairing) |
| 1736 | `rw` | `pairFstD_pairEncode` | theorem Complexity.pairFstD_pairEncode (TCSlib.Complexity.ClassNP.PolyTimePairing) |
| 1737 | `rw` | `this` | local hypothesis / let-bound name |
| 1740 | `simp` | `hmem` | local hypothesis / let-bound name |
| 1740 | `simp` | `decide_true` | theorem decide_true (Init.Core) |
| 1740 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 1740 | `simp` | `List.cons.injEq` | theorem List.cons.injEq (Init.Core) |
| 1740 | `simp` | `and_true` | theorem and_true (Init.SimpLemmas) |
| 1747 | `simp` | `hmem` | local hypothesis / let-bound name |
| 1747 | `simp` | `decide_false` | theorem decide_false (Init.Core) |
| 1747 | `simp` | `Bool.false_eq_true` | theorem Bool.false_eq_true (Init.Data.Bool) |
| 1747 | `simp` | `if_false` | theorem if_false (Init.ByCases) |
| 1747 | `simp` | `hpad` | local hypothesis / let-bound name |
| 1749 | `rw` | `hout` | local hypothesis / let-bound name |
| 1759 | `rw` | `e` | local hypothesis / let-bound name |

Counts by kind (first word): default: 31, goal: 24, local: 450, own: 37, simproc: 45, term: 8, theorem: 266
