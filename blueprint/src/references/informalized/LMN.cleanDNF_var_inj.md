<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: cleanDNF_var_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# In a cleaned DNF, a variable determines its literal

**Claim.** For every `d : DNF n`, every term `t ∈ cleanDNF d` and all
`l₁ l₂ ∈ t`, if `l₁.var = l₂.var` then `l₁ = l₂`. That is, no term of the
cleaned DNF mentions one variable twice — with either polarity.

**Proof.** Three steps.

1. `intro t ht l₁ hl₁ l₂ hl₂ hvar`.
2. `h_l1_l2 : ∃ t' ∈ d, t = dedupTermVar t'` — from `unfold cleanDNF at ht`
   plus `aesop` (membership in a `filter`-then-`map` image); `obtain ⟨t', ht', rfl⟩`
   substitutes `t = dedupTermVar t'`.
3. `exact dedupTermVar_var_inj t' l₁ hl₁ l₂ hl₂ hvar`, which carries the content:
   the accumulator invariant of `dedupTermVar`'s `foldr` keeps variables
   pairwise distinct, so equal variables force equal literals.

Note the filter step (`!termHasContradiction`) plays no role here — the
conclusion is a property of `dedupTermVar` alone.

**Used in.** `switching_bernoulli_dtDepth_dnf_general`, `CompressionStep.lean`,
`CircuitTreeManip.lean`, supplying the `hnd` hypothesis of
`switching_bernoulli_dtDepth_dnf`.
