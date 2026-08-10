<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: mergeGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Concatenation of two gate arrays

**Definition.** For any type `α` and any `m₁ m₂ : ℕ`, given `g₁ : Fin m₁ → α`
and `g₂ : Fin m₂ → α`, the array `mergeGates g₁ g₂ : Fin (m₁ + m₂) → α` is
defined by case split on the index value:

```
mergeGates g₁ g₂ j = if h : j.val < m₁ then g₁ ⟨j.val, h⟩ else g₂ ⟨j.val - m₁, _⟩
```

So indices `0, …, m₁ − 1` read off `g₁` and indices `m₁, …, m₁ + m₂ − 1` read off
`g₂` shifted down by `m₁`; the side condition `j.val - m₁ < m₂` in the `else`
branch is discharged by `omega`. The definition is purely index arithmetic — `α`
is arbitrary, and the LMN application instantiates it at `DNF n` (gate formulas)
and at `Bool` (gate values).

**Used in.** Every other lemma in `GateMerge.lean`: the two projection equations
`mergeGates_castAdd` / `mergeGates_natAdd` (both `@[simp]`), the reindexing
lemmas `reidx_eval_mergeGates_left` / `_right`, and the three
property-preservation lemmas `mergeGates_width`, `mergeGates_varInj`,
`mergeGates_nodup`.
