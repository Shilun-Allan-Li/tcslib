<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanCNF_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every clause of a cleaned CNF is duplicate-free

**Claim.** For every `c : CNF n` and every clause `t ∈ cleanCNF c`, `t.Nodup`.

**Proof.** One line after unfolding. `unfold cleanCNF`, then
`rcases List.mem_map.mp ht with ⟨t₀, -, rfl⟩` writes `t = dedupTermVar t₀` for
some `t₀` in the filtered list (the membership witness is discarded — it is not
needed), and `dedupTermVar_nodup t₀` finishes: the `foldr` in `dedupTermVar`
conses a literal only when no literal with the same variable is already in the
accumulator.

**Used in.** `switching_bernoulli_dtDepth_cnf_general` (its only caller), which
needs it as the `hnodup` hypothesis of `switching_bernoulli_dtDepth_cnf`. It is
the CNF-side twin of `cleanDNF_nodup`.
