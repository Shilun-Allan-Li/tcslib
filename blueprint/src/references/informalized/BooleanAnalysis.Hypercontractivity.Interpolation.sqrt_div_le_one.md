<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Duality.lean :: Interpolation.sqrt_div_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Square root of a ratio at most one is at most one

**Claim.** For reals `a, b` with `0 ≤ a`, `0 < b` and `a ≤ b`, we have
`Real.sqrt (a / b) ≤ 1`. A public arithmetic helper in the `Interpolation` namespace.

**Proof.** Two steps.

1. `rw [Real.sqrt_le_one]` turns the goal into `a / b ≤ 1`.
2. `div_le_one_iff.mpr (Or.inl ⟨hb, hab⟩)` — the branch "denominator positive and
   numerator at most denominator". ∎

**Note.** The non-negativity hypothesis `_ha` is unused (underscored).

**Used in.** `BooleanAnalysis.Hypercontractivity.general_one_function_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.high_norms_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.low_norms_hypercontractivity` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Bounds.lean`; `BooleanAnalysis.Hypercontractivity.bridging_hypercontractivity` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Duality.lean`.
