<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: exactMod_on_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `exactMod` computes the `MOD p` gate exactly on bits

**Claim.** Let `inputs : Fin width → ZMod p` take values in `{0, 1}`. Then the Fermat
indicator of the sum agrees with the `MOD p` gate applied to the corresponding bits:

`1 - (∑ i, inputs i) ^ (p - 1) = ((modGateOp p width).func (fun i ↦ bitify p (inputs i)) : ℕ)`

as elements of `ZMod p` (the right side is a `Fin 2` value, cast through `ℕ`).

**Proof.**

1. `hs` : `∑ i, ((bitify p (inputs i) : ℕ) : ZMod p) = ∑ i, inputs i`, by
   `Finset.sum_congr rfl` and `cast_bitify_eq (hinputs i)` termwise — the bits recover the
   original field values, so the gate sees the same sum.
2. Rewrite the left side as `if ∑ i, inputs i = 0 then 1 else 0` using
   `one_sub_pow_card_sub_one` (Fermat's little theorem in `ZMod p`).
3. `simp [modGateOp, hs]` unfolds the gate, whose body is the *same* `if`, now on the same
   sum by step 1.
4. `split_ifs <;> norm_num` discharges the two remaining `Fin 2 → ℕ → ZMod p` cast
   equalities (`1 = 1`, `0 = 0`).

**Used in.** The correctness obligation of the `MOD` branch of `exists_poly_for_gate`, and
of the corresponding branch in `RazborovSmolensky/CircuitDegree.lean:496`.
