# Inspection table (cp2, commit 53c3d0c2b3e301485ec05b6abcc3276dc6c6eef8)

Every `rw`/`rwa`/`erw`/`nth_rewrite`/`simp`/`simpa`/`simp_all`/`dsimp`/`unfold`/`show`/`change` argument on an added line of `git diff 72fcfbef 53c3d0c2 -- TCSlib/Complexity/SpaceComplexity/Padding.lean`. Kinds resolved by `Probe/EPadKinds.lean` in `namespace Complexity` with `open Turing`.

| line | tactic | argument | kind |
|---:|---|---|---|
| 98 | `rw` | `epadVirt` | own file: def `epadVirt` |
| 98 | `rw` | `if_pos h` | theorem if_pos (Init.Core) |
| 104 | `rw` | `epadVirt` | own file: def `epadVirt` |
| 104 | `rw` | `if_neg h` | theorem if_neg (Init.Core) |
| 110 | `rw` | `epadVirt_of_valid h` | own file: theorem `epadVirt_of_valid` |
| 111 | `rw` | `epadVirt_of_not_valid h` | own file: theorem `epadVirt_of_not_valid` |
| 121 | `rw` | `pairDecode_pairEncode` | theorem Turing.pairDecode_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 121 | `rw` | `Option.some.injEq` | theorem Option.some.injEq (Init.Core) |
| 121 | `rw` | `Prod.mk.injEq` | theorem Prod.mk.injEq (Init.Core) |
| 123 | `rw` | `LogProg.bitsVal_bits` | theorem Complexity.LogProg.bitsVal_bits (TCSlib.Complexity.SpaceComplexity.Machines.Bin) |
| 129 | `rw` | `LogProg.bitsVal_bits` | theorem Complexity.LogProg.bitsVal_bits (TCSlib.Complexity.SpaceComplexity.Machines.Bin) |
| 159 | `rw` | `h` | local hypothesis / let-bound name |
| 160 | `rw` | `h` | local hypothesis / let-bound name |
| 161 | `rw` | `h` | local hypothesis / let-bound name |
| 162 | `rw` | `h` | local hypothesis / let-bound name |
| 163 | `rw` | `h` | local hypothesis / let-bound name |
| 172 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 173 | `simp_all` | `(no lemma list)` | default simp set |
| 203 | `simpa` | `(no lemma list)` | default simp set |
| 207 | `rw` | `← eq` | local hypothesis / let-bound name |
| 207 | `rw` | `Function.update_eq_self` | theorem Function.update_eq_self (Mathlib.Logic.Function.Basic) |
| 207 | `rw` | `List.length_nil` | theorem List.length_nil (Init.Data.List.Basic) |
| 207 | `rw` | `Nat.add_zero` | theorem Nat.add_zero (Init.Core) |
| 207 | `rw` | `Function.update_eq_self` | theorem Function.update_eq_self (Mathlib.Logic.Function.Basic) |
| 208 | `rw` | `e` | local hypothesis / let-bound name |
| 212 | `rwa` | `astep_jeq htest` | local hypothesis / let-bound name |
| 212 | `rwa` | `if_pos eq` | theorem if_pos (Init.Core) |
| 215 | `simp` | `List.length_cons` | theorem List.length_cons (Init.Data.List.Basic) |
| 220 | `simpa` | `(no lemma list)` | default simp set |
| 220 | `simp` | `(no lemma list)` | default simp set |
| 224 | `rw` | `astep_jeq htest` | local hypothesis / let-bound name |
| 224 | `rw` | `if_neg hne` | theorem if_neg (Init.Core) |
| 228 | `rwa` | `astep_call hread` | local hypothesis / let-bound name |
| 228 | `rwa` | `vword_whole₁` | local hypothesis / let-bound name |
| 228 | `rwa` | `hb` | local hypothesis / let-bound name |
| 232 | `simp` | `(no lemma list)` | default simp set |
| 233 | `simp` | `(no lemma list)` | default simp set |
| 240 | `rw` | `hl` | local hypothesis / let-bound name |
| 240 | `rw` | `Nat.mul_succ` | theorem Nat.mul_succ (Init.Data.Nat.Basic) |
| 242 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 242 | `rw` | `Function.update_of_ne hpc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 246 | `rw` | `astep_inc hinc` | local hypothesis / let-bound name |
| 246 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 249 | `show` | `v₁ ptr + stride ≤ B` | goal restatement |
| 250 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 250 | `rw` | `Function.update_of_ne hpc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 251 | `rwa` | `hend` | local hypothesis / let-bound name |
| 251 | `rwa` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 251 | `rwa` | `← hv₂` | local hypothesis / let-bound name |
| 253 | `simp` | `hv₂` | local hypothesis / let-bound name |
| 253 | `simp` | `hv₁` | local hypothesis / let-bound name |
| 253 | `simp` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 253 | `simp` | `Function.update_of_ne hpl.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 253 | `simp` | `Function.update_of_ne hlc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 253 | `simp` | `Function.update_of_ne hpc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 255 | `rw` | `hl` | local hypothesis / let-bound name |
| 255 | `rw` | `Nat.mul_succ` | theorem Nat.mul_succ (Init.Data.Nat.Basic) |
| 257 | `simp` | `hv₂` | local hypothesis / let-bound name |
| 257 | `simp` | `hv₁` | local hypothesis / let-bound name |
| 257 | `simp` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 257 | `simp` | `Function.update_of_ne hpc.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 262 | `simp` | `(no lemma list)` | default simp set |
| 263 | `simp` | `hv₂` | local hypothesis / let-bound name |
| 263 | `simp` | `hv₁` | local hypothesis / let-bound name |
| 263 | `simp` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 263 | `simp` | `Function.update_of_ne hpc` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 264 | `simpa` | `Nat.mul_succ` | theorem Nat.mul_succ (Init.Data.Nat.Basic) |
| 264 | `simpa` | `Nat.add_assoc` | theorem Nat.add_assoc (Init.Data.Nat.Basic) |
| 264 | `simpa` | `Nat.add_comm stride` | theorem Nat.add_comm (Init.Data.Nat.Basic) |
| 267 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 270 | `simpa` | `(no lemma list)` | default simp set |
| 270 | `simp` | `(no lemma list)` | default simp set |
| 274 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 274 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 276 | `rwa` | `e` | local hypothesis / let-bound name |
| 278 | `simp` | `(no lemma list)` | default simp set |
| 280 | `simpa` | `(no lemma list)` | default simp set |
| 280 | `simpa` | `(no lemma list)` | default simp set |
| 282 | `rw` | `hfr r hr1 hr2` | local hypothesis / let-bound name |
| 282 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 282 | `rw` | `Function.update_of_ne hr1` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 282 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 282 | `rw` | `Function.update_of_ne hr2` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 304 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 304 | `simp` | `Nat.zero_mul` | theorem Nat.zero_mul (Init.Data.Nat.Basic) |
| 304 | `simp` | `Nat.add_zero` | theorem Nat.add_zero (Init.Core) |
| 305 | `simp_all` | `(no lemma list)` | default simp set |
| 306 | `rw` | `e` | local hypothesis / let-bound name |
| 310 | `rwa` | `astep_jz hml` | local hypothesis / let-bound name |
| 310 | `rwa` | `if_pos hk` | theorem if_pos (Init.Core) |
| 316 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 317 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 317 | `rw` | `Function.update_of_ne hkt.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 317 | `rw` | `ht` | local hypothesis / let-bound name |
| 318 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 318 | `rw` | `Function.update_of_ne hkp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 319 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 319 | `rw` | `Function.update_of_ne hkq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 322 | `rw` | `h₁t` | local hypothesis / let-bound name |
| 324 | `rw` | `← hv₂` | local hypothesis / let-bound name |
| 325 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 332 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 332 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 332 | `rw` | `Function.update_of_ne htq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 332 | `rw` | `h₁p` | local hypothesis / let-bound name |
| 332 | `rw` | `h₁q` | local hypothesis / let-bound name |
| 332 | `rw` | `Nat.one_mul` | theorem Nat.one_mul (Init.Data.Nat.Basic) |
| 336 | `rw` | `← hv₃` | local hypothesis / let-bound name |
| 338 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 340 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 340 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 340 | `rw` | `Function.update_of_ne htq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 340 | `rw` | `h₁p` | local hypothesis / let-bound name |
| 340 | `rw` | `h₁q` | local hypothesis / let-bound name |
| 340 | `rw` | `Nat.one_mul` | theorem Nat.one_mul (Init.Data.Nat.Basic) |
| 344 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 344 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 344 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 345 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 346 | `simp_all` | `(no lemma list)` | default simp set |
| 347 | `rw` | `key` | local hypothesis / let-bound name |
| 347 | `rw` | `key` | local hypothesis / let-bound name |
| 347 | `simp` | `htq` | local hypothesis / let-bound name |
| 347 | `simp` | `hkt.symm` | local hypothesis / let-bound name |
| 347 | `simp` | `ht` | local hypothesis / let-bound name |
| 348 | `rw` | `key` | local hypothesis / let-bound name |
| 348 | `rw` | `key` | local hypothesis / let-bound name |
| 348 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 348 | `simp` | `if_neg hkq.symm` | theorem if_neg (Init.Core) |
| 348 | `simp` | `if_neg hkp.symm` | theorem if_neg (Init.Core) |
| 348 | `simp` | `if_neg hpq` | theorem if_neg (Init.Core) |
| 349 | `rw` | `Nat.succ_mul` | theorem Nat.succ_mul (Init.Data.Nat.Basic) |
| 351 | `rw` | `astep_jz hml` | local hypothesis / let-bound name |
| 351 | `rw` | `if_neg (by omega)` | theorem if_neg (Init.Core) |
| 353 | `rw` | `astep_dec hmd` | local hypothesis / let-bound name |
| 353 | `rw` | `hk` | local hypothesis / let-bound name |
| 353 | `rw` | `Nat.add_sub_cancel` | theorem Nat.add_sub_cancel (Init.Data.Nat.Basic) |
| 353 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 358 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 358 | `simp` | `key` | local hypothesis / let-bound name |
| 359 | `simp_all` | `(no lemma list)` | default simp set |
| 361 | `rwa` | `e` | local hypothesis / let-bound name |
| 389 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 389 | `simp` | `pow_zero` | theorem pow_zero (Mathlib.Algebra.Group.Defs) |
| 389 | `simp` | `Nat.mul_one` | theorem Nat.mul_one (Init.Data.Nat.Basic) |
| 390 | `simp_all` | `(no lemma list)` | default simp set |
| 391 | `rw` | `eq` | local hypothesis / let-bound name |
| 395 | `rwa` | `astep_jz hpw` | local hypothesis / let-bound name |
| 395 | `rwa` | `if_pos he` | theorem if_pos (Init.Core) |
| 406 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 406 | `rw` | `Function.update_of_ne hdk.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 406 | `rw` | `hk` | local hypothesis / let-bound name |
| 412 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 412 | `rw` | `Function.update_of_ne hkt.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 412 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 412 | `rw` | `Function.update_of_ne hdt.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 412 | `rw` | `ht` | local hypothesis / let-bound name |
| 414 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 414 | `rw` | `Function.update_of_ne hkq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 414 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 414 | `rw` | `Function.update_of_ne hkp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 414 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 414 | `rw` | `Function.update_of_ne hdq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 414 | `rw` | `Function.update_of_ne hnd` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 414 | `rw` | `Function.update_of_ne hdp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 414 | `rw` | `hq` | local hypothesis / let-bound name |
| 414 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 414 | `rw` | `Nat.mul_comm` | theorem Nat.mul_comm (Init.Data.Nat.Basic) |
| 420 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 420 | `rw` | `Function.update_of_ne hkq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 420 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 420 | `rw` | `Function.update_of_ne hkp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 420 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 420 | `rw` | `Function.update_of_ne hdq.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 420 | `rw` | `Function.update_of_ne hnd` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 420 | `rw` | `Function.update_of_ne hdp.symm` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 420 | `rw` | `hq` | local hypothesis / let-bound name |
| 420 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 420 | `rw` | `Nat.mul_comm` | theorem Nat.mul_comm (Init.Data.Nat.Basic) |
| 426 | `rw` | `← hv₃` | local hypothesis / let-bound name |
| 427 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 427 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 427 | `rw` | `hval` | local hypothesis / let-bound name |
| 429 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 431 | `rw` | `hval` | local hypothesis / let-bound name |
| 436 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 436 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 443 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 443 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 443 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 443 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 443 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 443 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 444 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 445 | `simp_all` | `Nat.mul_comm` | theorem Nat.mul_comm (Init.Data.Nat.Basic) |
| 446 | `rw` | `key` | local hypothesis / let-bound name |
| 446 | `rw` | `key` | local hypothesis / let-bound name |
| 446 | `simp` | `hpq.symm` | local hypothesis / let-bound name |
| 446 | `simp` | `hdq.symm` | local hypothesis / let-bound name |
| 446 | `simp` | `hq` | local hypothesis / let-bound name |
| 447 | `rw` | `key` | local hypothesis / let-bound name |
| 447 | `simp` | `hkp` | local hypothesis / let-bound name |
| 447 | `simp` | `hdk.symm` | local hypothesis / let-bound name |
| 447 | `simp` | `hk` | local hypothesis / let-bound name |
| 447 | `rw` | `key` | local hypothesis / let-bound name |
| 447 | `simp` | `htp` | local hypothesis / let-bound name |
| 447 | `simp` | `hdt.symm` | local hypothesis / let-bound name |
| 447 | `simp` | `ht` | local hypothesis / let-bound name |
| 448 | `rw` | `key` | local hypothesis / let-bound name |
| 448 | `simpa` | `hnp` | local hypothesis / let-bound name |
| 448 | `simpa` | `hnd` | local hypothesis / let-bound name |
| 449 | `rw` | `key` | local hypothesis / let-bound name |
| 449 | `rw` | `key` | local hypothesis / let-bound name |
| 449 | `simp` | `↓reduceIte` | simproc reduceIte (Lean core) |
| 449 | `simp` | `if_neg hdp.symm` | theorem if_neg (Init.Core) |
| 449 | `simp` | `if_neg hnp` | theorem if_neg (Init.Core) |
| 449 | `simp` | `if_neg hnd` | theorem if_neg (Init.Core) |
| 450 | `rw` | `Nat.mul_assoc` | theorem Nat.mul_assoc (Init.Data.Nat.Basic) |
| 450 | `rw` | `← pow_succ'` | theorem pow_succ' (Mathlib.Algebra.Group.Defs) |
| 452 | `rw` | `astep_jz hpw` | local hypothesis / let-bound name |
| 452 | `rw` | `if_neg (by omega)` | theorem if_neg (Init.Core) |
| 454 | `rw` | `astep_dec hpd` | local hypothesis / let-bound name |
| 454 | `rw` | `he` | local hypothesis / let-bound name |
| 454 | `rw` | `Nat.add_sub_cancel` | theorem Nat.add_sub_cancel (Init.Data.Nat.Basic) |
| 454 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 457 | `rw` | `astep_clr hmv` | local hypothesis / let-bound name |
| 457 | `rw` | `← hv₄` | local hypothesis / let-bound name |
| 460 | `rw` | `astep_clr hmvc` | local hypothesis / let-bound name |
| 460 | `rw` | `← hv₆` | local hypothesis / let-bound name |
| 464 | `simp` | `Function.update_apply` | theorem Function.update_apply (Mathlib.Logic.Function.Basic) |
| 464 | `simp` | `key` | local hypothesis / let-bound name |
| 465 | `simp_all` | `pow_succ'` | theorem pow_succ' (Mathlib.Algebra.Group.Defs) |
| 465 | `simp_all` | `Nat.mul_assoc` | theorem Nat.mul_assoc (Init.Data.Nat.Basic) |
| 466 | `rwa` | `eq` | local hypothesis / let-bound name |
| 503 | `simp` | `epadVLAll` | own file: def `epadVLAll` |
| 504 | `simp` | `epadVLAll` | own file: def `epadVLAll` |
| 581 | `rw` | `ha'` | local hypothesis / let-bound name |
| 581 | `rw` | `pairDecode_pairEncode` | theorem Turing.pairDecode_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 581 | `rw` | `Option.some.injEq` | theorem Option.some.injEq (Init.Core) |
| 581 | `rw` | `Prod.mk.injEq` | theorem Prod.mk.injEq (Init.Core) |
| 585 | `rw` | `eq_pairEncode_of_pairDecode y a b h` | theorem Turing.eq_pairEncode_of_pairDecode (TCSlib.Complexity.TuringMachine.Encoding) |
| 585 | `rw` | `hb` | local hypothesis / let-bound name |
| 591 | `rw` | `ha` | local hypothesis / let-bound name |
| 591 | `rw` | `pairDecode_pairEncode` | theorem Turing.pairDecode_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 598 | `rw` | `List.eq_replicate_iff` | theorem List.eq_replicate_iff (Init.Data.List.Lemmas) |
| 602 | `rw` | `List.getD_eq_getElem?_getD` | theorem List.getD_eq_getElem?_getD (Init.Data.List.Lemmas) |
| 602 | `rw` | `List.getElem?_eq_getElem hi` | theorem List.getElem?_eq_getElem (Init.GetElem) |
| 602 | `rw` | `Option.getD_some` | theorem Option.getD_some (Init.Data.Option.Basic) |
| 608 | `rwa` | `List.getD_eq_getElem?_getD` | theorem List.getD_eq_getElem?_getD (Init.Data.List.Lemmas) |
| 608 | `rwa` | `List.getElem?_eq_getElem hi` | theorem List.getElem?_eq_getElem (Init.GetElem) |
| 608 | `rwa` | `Option.getD_some` | theorem Option.getD_some (Init.Data.Option.Basic) |
| 630 | `rw` | `← hs_def` | local hypothesis / let-bound name |
| 631 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 631 | `rw` | `epadS` | own file: def `epadS` |
| 632 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 632 | `rw` | `epadS` | own file: def `epadS` |
| 635 | `rw` | `h` | local hypothesis / let-bound name |
| 642 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 642 | `simp` | `epadS` | own file: def `epadS` |
| 646 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 646 | `simp` | `epadS` | own file: def `epadS` |
| 646 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 652 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 656 | `rw` | `h0` | local hypothesis / let-bound name |
| 656 | `rw` | `h1` | local hypothesis / let-bound name |
| 656 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 656 | `rw` | `h0` | local hypothesis / let-bound name |
| 656 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 659 | `simp` | `hd` | local hypothesis / let-bound name |
| 665 | `rw` | `h0` | local hypothesis / let-bound name |
| 665 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 667 | `rw` | `if_neg hnv` | theorem if_neg (Init.Core) |
| 670 | `simp` | `hd` | local hypothesis / let-bound name |
| 672 | `rw` | `hy'` | local hypothesis / let-bound name |
| 672 | `rw` | `length_pairEncode` | theorem Turing.length_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 673 | `rw` | `hy'` | local hypothesis / let-bound name |
| 673 | `rw` | `pairFstD_pairEncode` | theorem Complexity.pairFstD_pairEncode (TCSlib.Complexity.ClassNP.PolyTimePairing) |
| 683 | `rw` | `← hv₁` | local hypothesis / let-bound name |
| 686 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 686 | `rw` | `h0` | local hypothesis / let-bound name |
| 690 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 690 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 690 | `rw` | `hz 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 693 | `rw` | `← hv₂` | local hypothesis / let-bound name |
| 694 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 697 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 699 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 699 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 699 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 699 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 699 | `rw` | `h0` | local hypothesis / let-bound name |
| 699 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 704 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 707 | `rw` | `astep_half hc` | local hypothesis / let-bound name |
| 707 | `rw` | `h₂₂` | local hypothesis / let-bound name |
| 707 | `rw` | `hs` | local hypothesis / let-bound name |
| 707 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 709 | `rw` | `this` | local hypothesis / let-bound name |
| 712 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 716 | `rw` | `astep_half hc` | local hypothesis / let-bound name |
| 716 | `rw` | `h₂₂` | local hypothesis / let-bound name |
| 716 | `rw` | `hs` | local hypothesis / let-bound name |
| 719 | `rw` | `astep_half hc'` | local hypothesis / let-bound name |
| 719 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 719 | `rw` | `Function.update_idem` | theorem Function.update_idem (Mathlib.Logic.Function.Basic) |
| 719 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 721 | `rw` | `this` | local hypothesis / let-bound name |
| 725 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 725 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 725 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 725 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 725 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 725 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 725 | `rw` | `h0` | local hypothesis / let-bound name |
| 725 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 728 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 728 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 728 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 728 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 728 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 728 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 728 | `rw` | `h1` | local hypothesis / let-bound name |
| 732 | `rw` | `h` | local hypothesis / let-bound name |
| 732 | `simp` | `(no lemma list)` | default simp set |
| 733 | `rw` | `h` | local hypothesis / let-bound name |
| 733 | `simp` | `(no lemma list)` | default simp set |
| 734 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 734 | `rw` | `Function.update_of_ne h2` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 734 | `rw` | `hv₂` | local hypothesis / let-bound name |
| 734 | `rw` | `Function.update_of_ne h2` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 734 | `rw` | `hv₁` | local hypothesis / let-bound name |
| 734 | `rw` | `Function.update_of_ne h0'` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 740 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 740 | `simp` | `epadS` | own file: def `epadS` |
| 744 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 744 | `simp` | `epadS` | own file: def `epadS` |
| 744 | `simp` | `if_true` | theorem if_true (Init.ByCases) |
| 748 | `rw` | `hs_def` | local hypothesis / let-bound name |
| 752 | `rw` | `hv₃0` | local hypothesis / let-bound name |
| 752 | `rw` | `hv₃1` | local hypothesis / let-bound name |
| 752 | `rw` | `hlen` | local hypothesis / let-bound name |
| 752 | `rw` | `Nat.mul_add` | theorem Nat.mul_add (Init.Data.Nat.Basic) |
| 753 | `rw` | `hv₃r 3 (by decide)` | local hypothesis / let-bound name |
| 753 | `rw` | `hz 3 (by decide) (by decide)` | local hypothesis / let-bound name |
| 756 | `rw` | `hy'` | local hypothesis / let-bound name |
| 756 | `rw` | `pairEncode_getD_snd` | theorem Complexity.pairEncode_getD_snd (TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess) |
| 757 | `rw` | `hv₃0` | local hypothesis / let-bound name |
| 757 | `rw` | `← h` | local hypothesis / let-bound name |
| 757 | `rw` | `← Nat.mul_add` | theorem Nat.mul_add (Init.Data.Nat.Basic) |
| 763 | `rw` | `← hv₄` | local hypothesis / let-bound name |
| 765 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 767 | `rw` | `hv₃r 3 (by decide)` | local hypothesis / let-bound name |
| 767 | `rw` | `hz 3 (by decide) (by decide)` | local hypothesis / let-bound name |
| 770 | `rw` | `h` | local hypothesis / let-bound name |
| 770 | `simp` | `(no lemma list)` | default simp set |
| 771 | `rw` | `h` | local hypothesis / let-bound name |
| 771 | `simp` | `(no lemma list)` | default simp set |
| 772 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 772 | `rw` | `Function.update_of_ne h3` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 772 | `rw` | `Function.update_of_ne h0'` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 772 | `rw` | `hv₃r r (by omega)` | local hypothesis / let-bound name |
| 774 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 774 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 774 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 774 | `rw` | `hv₃` | local hypothesis / let-bound name |
| 774 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 777 | `rw` | `hv₄` | local hypothesis / let-bound name |
| 777 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 777 | `rw` | `hv₃r 3 (by decide)` | local hypothesis / let-bound name |
| 777 | `rw` | `hz 3 (by decide) (by decide)` | local hypothesis / let-bound name |
| 777 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 781 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 783 | `rw` | `e1` | local hypothesis / let-bound name |
| 785 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 785 | `rw` | `hv₄r 4 (by decide)` | local hypothesis / let-bound name |
| 785 | `rw` | `hz 4 (by decide) (by decide)` | local hypothesis / let-bound name |
| 787 | `rw` | `eC` | local hypothesis / let-bound name |
| 787 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 787 | `rw` | `hv₄r 4 (by decide)` | local hypothesis / let-bound name |
| 787 | `rw` | `hz 4 (by decide) (by decide)` | local hypothesis / let-bound name |
| 787 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 789 | `rw` | `← hv₅` | local hypothesis / let-bound name |
| 791 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 794 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 796 | `rw` | `e1` | local hypothesis / let-bound name |
| 798 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 798 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 798 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 798 | `rw` | `hv₄r 8 (by decide)` | local hypothesis / let-bound name |
| 798 | `rw` | `hz 8 (by decide) (by decide)` | local hypothesis / let-bound name |
| 802 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 802 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 802 | `rw` | `hv₄r 8 (by decide)` | local hypothesis / let-bound name |
| 802 | `rw` | `hz 8 (by decide) (by decide)` | local hypothesis / let-bound name |
| 804 | `rw` | `eD` | local hypothesis / let-bound name |
| 804 | `rw` | `cond_true` | theorem cond_true (Init.SimpLemmas) |
| 804 | `rw` | `hv₅8` | local hypothesis / let-bound name |
| 804 | `rw` | `Nat.zero_add` | theorem Nat.zero_add (Init.Data.Nat.Basic) |
| 806 | `rw` | `← hv₆` | local hypothesis / let-bound name |
| 808 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 811 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 811 | `rw` | `Function.update_of_ne h8` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 811 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 811 | `rw` | `Function.update_of_ne h4` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 820 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 820 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 821 | `rw` | `hv₆r 5 (by decide) (by decide)` | local hypothesis / let-bound name |
| 821 | `rw` | `hv₄r 5 (by decide)` | local hypothesis / let-bound name |
| 821 | `rw` | `hz 5 (by decide) (by decide)` | local hypothesis / let-bound name |
| 822 | `rw` | `hv₆r 6 (by decide) (by decide)` | local hypothesis / let-bound name |
| 822 | `rw` | `hv₄r 6 (by decide)` | local hypothesis / let-bound name |
| 822 | `rw` | `hz 6 (by decide) (by decide)` | local hypothesis / let-bound name |
| 823 | `rw` | `hv₆r 7 (by decide) (by decide)` | local hypothesis / let-bound name |
| 823 | `rw` | `hv₄r 7 (by decide)` | local hypothesis / let-bound name |
| 823 | `rw` | `hz 7 (by decide) (by decide)` | local hypothesis / let-bound name |
| 824 | `rw` | `hv₆r 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 824 | `rw` | `hv₄2` | local hypothesis / let-bound name |
| 825 | `rw` | `hv₆r 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 825 | `rw` | `hv₄2` | local hypothesis / let-bound name |
| 825 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 825 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 825 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 825 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 828 | `rw` | `hv₆r 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 828 | `rw` | `hv₄2` | local hypothesis / let-bound name |
| 828 | `rw` | `hv₆` | local hypothesis / let-bound name |
| 828 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 828 | `rw` | `hv₅` | local hypothesis / let-bound name |
| 828 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 830 | `rw` | `hp6` | local hypothesis / let-bound name |
| 833 | `rw` | `← hv₇` | local hypothesis / let-bound name |
| 835 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 839 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 839 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 839 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 839 | `rw` | `hv₆r 3 (by decide) (by decide)` | local hypothesis / let-bound name |
| 839 | `rw` | `hv₄3` | local hypothesis / let-bound name |
| 841 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 841 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 843 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 843 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 843 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 843 | `rw` | `hv₆r 2 (by decide) (by decide)` | local hypothesis / let-bound name |
| 843 | `rw` | `hv₄2` | local hypothesis / let-bound name |
| 849 | `rw` | `hv₇` | local hypothesis / let-bound name |
| 849 | `rw` | `Function.update_of_ne h4` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 849 | `rw` | `Function.update_of_ne h8` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 849 | `rw` | `hv₆r r h4 h8` | local hypothesis / let-bound name |
| 849 | `rw` | `hv₄r r (by omega)` | local hypothesis / let-bound name |
| 852 | `rw` | `hval` | local hypothesis / let-bound name |
| 852 | `rw` | `epad_eq_replicate_iff` | own file: theorem `epad_eq_replicate_iff` |
| 855 | `rw` | `hv₇2` | local hypothesis / let-bound name |
| 855 | `rw` | `hfst` | local hypothesis / let-bound name |
| 860 | `show` | `(3 : Fin 18) ≠ 4` | goal restatement |
| 861 | `rw` | `astep_jeq hcmp` | local hypothesis / let-bound name |
| 861 | `rw` | `hv₇3` | local hypothesis / let-bound name |
| 861 | `rw` | `hv₇4` | local hypothesis / let-bound name |
| 863 | `rw` | `if_pos (hiff.mp hv')` | theorem if_pos (Init.Core) |
| 864 | `rwa` | `if_pos hv'` | theorem if_pos (Init.Core) |
| 865 | `rw` | `if_neg (fun h => hv' (hiff.mpr h))` | theorem if_neg (Init.Core) |
| 866 | `rwa` | `if_neg hv'` | theorem if_neg (Init.Core) |
| 871 | `simpa` | `(no lemma list)` | default simp set |
| 876 | `rw` | `hfr r (hfar r hr9 0 (by decide)) (hfar r hr9 3 (by decide))` | local hypothesis / let-bound name |
| 876 | `rw` | `hv₃r r (by omega)` | local hypothesis / let-bound name |
| 877 | `rw` | `if_neg hnv` | theorem if_neg (Init.Core) |
| 889 | `simp` | `(no lemma list)` | default simp set |
| 906 | `show` | `inputBitLang ∈ LOGSPACE` | goal restatement |
| 908 | `show` | `inputLenLang ∈ LOGSPACE` | goal restatement |
| 918 | `show` | `MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _ ∧` | goal restatement |
| 957 | `rw` | `show epadS false * j = j from Nat.one_mul j` | term (an inline `show … from …` equation) |
| 957 | `show` | `epadS false * j = j` | goal restatement |
| 961 | `rw` | `Function.update_of_ne (by decide)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 962 | `rw` | `Function.update_self` | theorem Function.update_self (Mathlib.Logic.Function.Basic) |
| 964 | `rw` | `Function.update_of_ne (fun h => by rw [h] at h2; simp at h2)` | theorem Function.update_of_ne (Mathlib.Logic.Function.Basic) |
| 964 | `rw` | `h` | local hypothesis / let-bound name |
| 964 | `simp` | `(no lemma list)` | default simp set |
| 968 | `rw` | `indicator_eq_decide` | local hypothesis / let-bound name |
| 969 | `rw` | `if_pos hv` | theorem if_pos (Init.Core) |
| 969 | `rw` | `hy` | local hypothesis / let-bound name |
| 970 | `show` | `epadVA C d (.inr .yes) = .ret true` | goal restatement |
| 972 | `rw` | `indicator_eq_decide` | local hypothesis / let-bound name |
| 973 | `rw` | `if_neg hv` | theorem if_neg (Init.Core) |
| 973 | `rw` | `hy` | local hypothesis / let-bound name |
| 974 | `show` | `epadVA C d (.inr .no) = .ret false` | goal restatement |

Counts by kind (first word): default: 23, goal: 8, local: 265, own: 13, simproc: 2, term: 1, theorem: 172
