<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanDNF_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every term of a cleaned DNF is duplicate-free

**Claim.** For every `d : DNF n` and every term `t ∈ cleanDNF d`, `t.Nodup`.

**Proof.** Four lines, no mathematical content beyond unfolding.

1. `rw [cleanDNF] at ht` exposes `t ∈ (d.filter _).map dedupTermVar`.
2. `rcases List.mem_map.mp ht with ⟨t₀, ht₀, rfl⟩` names the preimage, so the
   goal becomes `(dedupTermVar t₀).Nodup`.
3. `apply dedupTermVar_nodup`, which is the real statement: the `foldr` in
   `dedupTermVar` only conses a literal when no literal with the same variable
   is already in the accumulator, so the result has no repeats.

**Used in.** `switching_bernoulli_dtDepth_dnf_general`, `CompressionStep.lean`,
`CircuitTreeManip.lean` — a granular repackaging of `dedupTermVar_nodup` at the
DNF level, in the exact shape the `hnodup` hypothesis of
`switching_bernoulli_dtDepth_dnf` wants.
