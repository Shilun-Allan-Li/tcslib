<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: mem_filter_freeVars_zipIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reading off the filter of free-variable literals

**Claim.** If a pair `p = (l, i)` occurs in
`(t_clause.zipIdx).filter (fun x => x.1.var ∈ ρ₀.freeVars)`, then `p ∈ t_clause.zipIdx`
and `ρ₀ p.1.var = none`.

**Proof.** Bookkeeping only.

1. `List.mem_filter.mp` splits the hypothesis into membership in
   `t_clause.zipIdx` (the first component of the conclusion) and the filter
   predicate.
2. The predicate `p.1.var ∈ ρ₀.freeVars` unfolds to `(ρ₀ p.1.var).isNone`, i.e.
   `ρ₀ p.1.var = none` — `simp [Restriction.freeVars, Finset.mem_filter,
   Option.isNone_iff_eq_none]`.

**Used in.** `go_roundtrip_gen`: after the encoder's clause literal list is
`generalize`d to an opaque `fl :: fls`, this is what recovers the two facts the
invariant lemmas need about its elements (`hmem_zip`, `hfree_lits`).
