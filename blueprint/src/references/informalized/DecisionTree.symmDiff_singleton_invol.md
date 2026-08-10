<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: symmDiff_singleton_invol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Symmetric difference with a singleton is an involution

**Claim.** For `i : Fin n`, the map `S ↦ S ∆ {i}` on `Finset (Fin n)` is
involutive (`Function.Involutive`): applying it twice returns `S`.

**Proof.** Immediate from
`simp only [symmDiff_assoc, symmDiff_self, symmDiff_bot]`, i.e.
`(S ∆ {i}) ∆ {i} = S ∆ ({i} ∆ {i}) = S ∆ ⊥ = S`.

This is a `private` one-line helper; its only role is to supply a bijection.

**Used in.** `sum_symmDiff_reindex`, which feeds
`(symmDiff_singleton_invol i).bijective` to `Fintype.sum_bijective` to reindex
a sum over all frequencies.
