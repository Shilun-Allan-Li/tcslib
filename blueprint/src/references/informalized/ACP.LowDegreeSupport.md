<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: LowDegreeSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Supports of squarefree monomials of degree at most `D`

**Definition.** `LowDegreeSupport n D` is the subtype
`{s : Finset (Fin n) // s.card ≤ D}`: a set of variable indices of size at most `D`. Each
such `s` names the squarefree monomial `∏ i ∈ s, X i`, so `LowDegreeSupport n D` indexes
the multilinear monomials of degree at most `D` in `n` variables.

**Remark.** It is a plain index type, deliberately kept as a subtype rather than a `Finset`
so that a coefficient family can be written as a function
`LowDegreeSupport n D → K` (see `lowDegreeSquarefreePolynomial`). The file also supplies
`lowDegreeSupportFintype` and `lowDegreeSupportDecidableEq`, both obtained by
`classical` + `infer_instance` after `unfold LowDegreeSupport`, and its cardinality is
bounded by `∑ t ∈ range (D + 1), n.choose t` in `lowDegreeSupport_card_le_binomial_sum`.
