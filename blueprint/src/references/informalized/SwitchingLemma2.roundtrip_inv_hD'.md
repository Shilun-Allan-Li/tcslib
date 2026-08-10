<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: roundtrip_inv_hD' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The ρ₀-invariant survives one clause block

**Claim.** Let `lits` be literals of `t_clause` whose variables are free under
`ρ₀` (`hfree_lits`, `hmem_zip`), and let `ρ₀_dec` agree with `ρ₀` at every
variable `ρ₀` fixes (`hD`). Write `pcl := processClauseLits lits path ρ₀ σ`.
Then for every `v` with `pcl.2.1 v ≠ none`, folding the decoder's ρ₀-updates
(`Function.update ρ₀' l.var (some e.2)` for the literal `l` at position `e.1`
of `t_clause`) over the aux block `pcl.2.2.2`, starting from `ρ₀_dec`, gives
`pcl.2.1 v` — the encoder's own value at `v`.

**Proof.** `by_cases` on whether `v` was already fixed before this clause.

1. `ρ₀ v = none`, so `v` is one of the variables this block fixes: the fold sets
   `v` to exactly the direction the encoder recorded
   (`processClauseLits_foldl_rho_eq_of_set`, `convert … using 1`).
2. `ρ₀ v ≠ none`: then no literal of `lits` mentions `v`
   (`hnone : ∀ p ∈ lits, p.1.var ≠ v`, from `hfree_lits` by `grind`), hence no
   aux entry of the block targets `v` (`processClauseLits_aux_ne_nonfree`) and
   the fold is inert (`foldl_rho_stable`). It therefore leaves `ρ₀_dec v`, which
   is `ρ₀ v` by `hD`, and that is `pcl.2.1 v` by
   `processClauseLits_rho_stable`.

**Used in.** `go_roundtrip_gen`, side goal `hD'`: it re-establishes the `hD`
hypothesis for the induction step with the folded decoder state in place of
`ρ₀_dec`. It is the `ρ₀`-side twin of `roundtrip_inv_hC'`.
