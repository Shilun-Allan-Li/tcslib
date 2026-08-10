<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity.lean :: dtDepth_composeRestr_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Composing restrictions only decreases decision-tree depth

**Claim.** For every `f : (Fin n → Bool) → Bool` and all `ρ₁ ρ₂ : Restriction n`,
`dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) ≤ dtDepth (restrictFn f ρ₁)`, where
`composeRestr ρ₁ ρ₂ i = (ρ₁ i).orElse (fun _ => ρ₂ i)` gives `ρ₁` priority and
lets `ρ₂` fix the coordinates `ρ₁` left free.

**Proof.** Reduce to the one-restriction case.

1. `suffices` the pointwise identity
   `restrictFn f (composeRestr ρ₁ ρ₂) = restrictFn (restrictFn f ρ₁) ρ₂`; given
   it, `rw [h]` and `dtDepth_restrictFn_le' _ ρ₂` finish.
2. For the identity: `ext x`, unfold `restrictFn`, then `congr 1; ext i` reduces
   to comparing the two extended inputs coordinatewise.
3. Unfolding `composeRestr` and `Restriction.extend` and casing on `ρ₁ i`
   (`cases ρ₁ i <;> simp [Option.getD]`) settles both coordinates: if `ρ₁` fixes
   `i` that value is used on both sides; otherwise both sides fall through to
   `ρ₂ i` and then to `x i`.

**Remark.** Only the identity in step 2 is specific to `composeRestr`; the
monotonicity itself is just `dtDepth_restrictFn_le'` applied to the already
restricted function.

**Used in.** `bernoulliRestrProb_dtDepth_compose_le`, where it shows that the
inner (second-stage) failure probability vanishes whenever the first stage
already achieved `dtDepth ≤ t`.
