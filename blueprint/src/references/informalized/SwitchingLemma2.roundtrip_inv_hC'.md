<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: roundtrip_inv_hC' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The σ-invariant survives one clause block

**Claim.** Let `lits` be free literals of `t_clause` under `ρ₀` (`hfree_lits`,
`hmem_zip`), let `σ` be free wherever `ρ₀` is (`hE`), and let `σ_dec` agree with
`σ` at every variable fixed by `ρ₀` (`hC`). Write `pcl := processClauseLits lits path ρ₀ σ`.
Then for every `v` fixed by `pcl.2.1`, folding the decoder's σ-updates
(`Function.update σ' l.var none` at each entry's literal) over the aux block
`pcl.2.2.2`, starting from `σ_dec`, gives `σ v`.

**Proof.** `by_cases` on whether `v` was already fixed before this clause.

1. `ρ₀ v = none` (so `v` is one of the literals fixed by this block): the fold
   clears `v`, giving `none` (`processClauseLits_foldl_sigma_none`), and `σ v = none`
   by `hE` — the `simp_all` normalises the goal to exactly that form.
2. `ρ₀ v ≠ none`: no entry of the block targets `v`
   (`processClauseLits_aux_ne_nonfree`, whose side condition `∀ p ∈ lits, p.1.var ≠ v`
   follows from `hfree_lits` by `grind`), so the fold is inert
   (`foldl_sigma_stable`) and leaves `σ_dec v`, which is `σ v` by `hC`.

**Used in.** `go_roundtrip_gen`, side goal `hC'`: it re-establishes the `hC`
hypothesis for the induction step with the folded decoder state in place of `σ_dec`.
