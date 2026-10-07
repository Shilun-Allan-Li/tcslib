<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegreeSupportSigmaMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tagging a low-degree support by its exact cardinality

**Definition.** `lowDegreeSupportSigmaMap n D` sends a low-degree support
`s : LowDegreeSupport n D` (a `Finset (Fin n)` with `s.card ≤ D`) to the dependent pair
`⟨⟨s.1.card, _⟩, ⟨s.1, rfl⟩⟩` in
`Σ t : Fin (D + 1), {u : Finset (Fin n) // u.card = t.1}`. The `Fin (D + 1)` component is
the exact cardinality of `s`, legitimate because `Nat.lt_succ_of_le s.2` turns `s.card ≤ D`
into `s.card < D + 1`; the second component is `s` itself, whose cardinality condition
holds by `rfl`.

**Remark.** Only a map, not an equivalence: the docstring says this is deliberate, since
building the inverse would require dependent-equality bookkeeping. Injectivity is all the
counting argument needs.

**Used in.** `lowDegreeSupport_card_le_binomial_sum`, where injectivity of this map plus
`Fintype.card_sigma` gives the bound `∑ t ∈ range (D + 1), n.choose t`.
