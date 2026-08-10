<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: sqrt_div_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Square root of a ratio at most one is at most one

**Claim.** For reals `a, b` with `0 ≤ a`, `0 < b` and `a ≤ b`, we have
`Real.sqrt (a / b) ≤ 1`. A `private` arithmetic helper, nothing more.

**Proof.** Two steps.

1. `rw [Real.sqrt_le_one]` turns the goal into `a / b ≤ 1`.
2. `div_le_one_iff.mpr (Or.inl ⟨hb, hab⟩)` — the branch "denominator positive and
   numerator at most denominator". ∎

**Note.** The non-negativity hypothesis `_ha` is unused (underscored).

**Used in.** The noise-parameter bounds `ρ ≤ 1` for `ρ = √((p-1)/(u-1))` in
`bridging_hypercontractivity` and in the low/high-norm interpolation theorems
later in the same file (5 call sites).
