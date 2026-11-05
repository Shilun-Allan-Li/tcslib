<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanDNF_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cleaning a DNF does not increase its width

**Claim.** `(cleanDNF d).width ≤ d.width` for every `d : DNF n`, where
`cleanDNF d` filters out the contradictory terms and de-duplicates each
surviving term by variable, and `DNF.width` is `(d.map Term.width).foldr max 0`.

**Proof.** After `simp_all [cleanDNF, DNF.width]` the goal is a comparison of
two `foldr max 0`s.

1. Reduce to a pointwise statement with the auxiliary
   `h_foldr_max_le : (∀ x ∈ l1, x ≤ l2.foldr max 0) → l1.foldr max 0 ≤ l2.foldr max 0`
   (`induction l1 <;> aesop`), then `apply` it and `intro x hx`.
2. Unpack `x`: `grind` produces `t ∈ d` with `x = Term.width (dedupTermVar t)`
   and `!termHasContradiction t` — filtering only removes terms and mapping
   only rewrites them.
3. `dedupTermVar_width_le t` gives `x ≤ t.width`.
4. `t.width` occurs in `d.map Term.width` (`List.mem_map.mpr`), and a second
   `foldr max` auxiliary (`t.width ∈ l → t.width ≤ l.foldr max 0`) bounds it by
   `d.width`. Chain with `le_trans`.

**Used in.** `switching_bernoulli_dtDepth_dnf_general`, and downstream in
`CompressionStep.lean` / `CircuitTreeManip.lean`, where a width hypothesis on
`d` must be transported to `cleanDNF d`.
