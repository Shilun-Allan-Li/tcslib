# fa progress (U9 CarrySave, U10 Compare)

BITS-LEMMA: no existing TCSlib/Mathlib/core lemma gives the value of the bit list `(range p).map c.testBit`
through a reader of `Adder.lean`'s `bitsVal`/`prefixVal`. Candidates checked: AdderLanguage.lean:72
`bitsVal_natToBits` (needs `natToBits` = `List.ofFn ...`, no reader of natToBits elements -> unusable under Rule 10);
CfgRecord.lean:150 `binDigits` (no value lemma); LupanovGates.lean:123 `testBit_ofBits` (its `ofBits` is not bridged to
`bitsVal`); Bin.lean/Word.lean `bitsVal` are `Complexity.LogProg.bitsVal`/other (no testBit list lemma); Batteries
`Nat.ofBits`/`testBit_ofBits_lt` (Fin-function, no bridge); core `Nat.mod_two_pow_succ` is PRIVATE (Init/Data/BitVec/Bitblast.lean:163).
Route (planned for Compare): private helper `prefixVal_testBit (c p : ℕ) : prefixVal c.testBit p = c % 2 ^ p`, by induction
on p with `prefixVal_zero`, `prefixVal_succ`, core `Nat.mod_pow_succ` (Init/Data/Nat/Mod.lean:76) and core
`Nat.toNat_testBit` (Init/Data/Nat/Bitwise/Lemmas.lean:138); then `bitsVal_eq_prefixVal` + `prefixVal_congr`
(getD of the mapped range is `c.testBit j` for `j < p`) gives `bitsVal ((range p).map c.testBit) = c % 2 ^ p`
(and `= c` for `c < 2 ^ p` by `Nat.mod_eq_of_lt`). Promotion request candidate for Adder.lean.

## Plan
- CarrySave: private helpers `maxDepth_le_of_forall`, `maxFaninL_le_of_forall` (Addendum A forms); a bit-level
  helper for csaStep_val; layer lemmas for csaReduce (value, length, depth, fan-in) by csaLayer induction;
  `Nat.repeat` iteration by induction on count; csaLevels_le by strong induction.
- Compare: helpers maxDepth/maxFaninL_le_of_forall (Addendum A), prefixVal_testBit, carry unrolling.
11:29 CarrySave F5 proved (csaStep_val, depth_csaStep_le, maxFaninL_csaStep_le); log CS-001 rc 0; 4 sorry left (F6)
11:33 CarrySave ALL 7 targets proved (F5+F6), 0 sorry, 0 warnings; log CS-007 rc 0; snapshot snapshots/CarrySave-final.lean (lead may integrate). Starting Compare.
11:41 Compare ALL 7 targets proved (F7+F8), 0 sorry, 0 warnings. Final: CS-008 (CarrySave, rc 0, 0 err/warn) then CMP-004 (Compare, rc 0, 0 err/warn). Local seal probes SealCS-002, SealCMP-002 rc 0. Snapshots snapshots/{CarrySave,Compare}-final.lean. DONE.
