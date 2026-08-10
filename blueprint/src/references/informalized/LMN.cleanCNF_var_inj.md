<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanCNF_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# In a cleaned CNF, a variable determines its literal

**Claim.** For every `c : CNF n`, every clause `t ∈ cleanCNF c` and all
`l₁ l₂ ∈ t`, if `l₁.var = l₂.var` then `l₁ = l₂` — no clause of the cleaned CNF
mentions a variable twice, with either polarity.

**Proof.** One line after unfolding.

1. `unfold cleanCNF`, `intro t ht l₁ hl₁ l₂ hl₂ hvar`.
2. `rcases List.mem_map.mp ht with ⟨t₀, -, rfl⟩` rewrites `t` as
   `dedupTermVar t₀` (the filter-membership witness is dropped, being irrelevant).
3. `exact dedupTermVar_var_inj t₀ l₁ hl₁ l₂ hl₂ hvar`.

All content sits in `dedupTermVar_var_inj`; this is only the CNF-level
repackaging (and the exact twin of `cleanDNF_var_inj`, since `cleanCNF` and
`cleanDNF` are literally the same function on `List (Term n)`).

**Used in.** `switching_bernoulli_dtDepth_cnf_general` (its only caller), as the
`hnd` hypothesis of `switching_bernoulli_dtDepth_cnf`.
