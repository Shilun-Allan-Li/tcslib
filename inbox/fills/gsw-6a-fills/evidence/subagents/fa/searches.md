# fa duplication searches (U9 CarrySave, U10 Compare)

Tools: grep over `TCSlib/`, `audits/`, `.lake/packages/mathlib/Mathlib`, `.lake/packages/batteries`, toolchain
`src/lean/Init` (Lean 4.25.0). Each helper name was grepped (`grep -rnw <name> TCSlib audits`): 0 hits for all.

| Query | Where | Result |
|---|---|---|
| `maxDepth_append`, `maxDepth_le`, `maxFaninL_append`, `maxFaninL_le`, `theorem.*maxDepth`, `theorem.*maxFaninL` | TCSlib, audits | only Basic.lean readers (nil/cons/depth_le_maxDepth/maxFanin_le_maxFaninL); private `maxDepth_map`/`maxFaninL_map` (TreeDAG.lean:407/420), private `maxDepth_map_le`/`maxFaninL_map_le` (TreeNCAC.lean:215/226) -> not reusable (private); Addendum A family `maxDepth_le_of_forall`/`maxFaninL_le_of_forall` written |
| `prefixVal` uses outside Adder | TCSlib | none (only Adder.lean and the docstrings of my files) -> `prefixVal_eq_of_false`, `prefixVal_fullAdder`, `prefixVal_testBit` are new |
| `testBit` lemmas (`theorem/lemma .*testBit`) | TCSlib | LupanovGates.lean:92/107/123 (`heapPath`, `ofBits` - not bridged to `bitsVal`), CfgRecord.lean:150 `binDigits_eq` (no value lemma), Arithmetic.lean `natToBits_*` (Fin-function `natToBits`, crypto) |
| `bitsVal` lemmas | TCSlib | AdderLanguage.lean:72 `bitsVal_natToBits` (needs elements of `natToBits = List.ofFn ...`, no reader -> Rule 10 blocks); Bin.lean/Word.lean/ClassP lemmas are about other `bitsVal`s (`Complexity.LogProg.bitsVal` etc.) |
| `testBit` + `range`/`ofDigits`/`sum`/`mod_two_pow` | Mathlib, Batteries | no list-of-testBit value lemma; Batteries `Nat.ofBits`/`testBit_ofBits_lt` (Fin-function, no bridge) |
| `mod_two_pow_succ`, `mod_pow_succ`, `toNat_testBit` | core Init | `Nat.mod_two_pow_succ` is PRIVATE (Init/Data/BitVec/Bitblast.lean:163); public `Nat.mod_pow_succ` (Init/Data/Nat/Mod.lean:76) and `Nat.toNat_testBit` (Init/Data/Nat/Bitwise/Lemmas.lean:138) used |
| `Nat.repeat` equation lemmas (`repeat_succ`, `repeat_zero`, `Nat.repeat`) | core, Mathlib, Batteries | none; used `show`/`change`/`rfl` steps and Mathlib `Function.iterate_succ_apply`, `iterate_succ_apply'`, `iterate_zero_apply` instead of a `Nat.repeat` helper |
| `getD` lemmas | core, Mathlib Data/List/GetD.lean | used `List.getD_map`, `getD_eq_getElem`, `getD_eq_default`, `getD_cons_zero/succ`, `getD_nil`; no "`getD ∈`" lemma (`getD_mem`, `mem_getD`: none) -> `mem_flatten_of_mem_getD` uses core `List.mem_flatten_of_mem` |
| `carryBit` characterisation | TCSlib | only Adder.lean (def, `carryBit_zero/succ`, `prefixVal_add`) -> `carryBit_eq_true_iff` new |
| full adder summed (`prefixVal_add`) | Adder.lean:405 | ripple form with `sumBit`/`carryBit`; not applicable to the carry-save words (bits given pointwise) -> `prefixVal_fullAdder` new |
| `Nat.clog` lemmas | Mathlib Data/Nat/Log.lean | `clog_pos` (292), `clog_of_two_le` (289), `clog_mono_right` (341) used |
