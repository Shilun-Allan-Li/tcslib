<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: lowDegreeSupport_card_le_binomial_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Counting low-degree squarefree supports

**Claim.** `Fintype.card (LowDegreeSupport n D) ≤ ∑ t ∈ Finset.range (D + 1), n.choose t`:
the number of subsets of `Fin n` of size at most `D` is at most the usual binomial sum.

**Proof.**
- Abbreviate `T := Σ t : Fin (D + 1), {s : Finset (Fin n) // s.card = t.1}`, the sets
  graded by their exact size.
- `hinj`: `lowDegreeSupportSigmaMap n D` is injective. Given a pair equal under the map,
  `congrArg (fun z : T => z.2.1)` extracts equality of the underlying finsets, and
  `Subtype.ext` with `simpa [lowDegreeSupportSigmaMap]` lifts it back to equality in
  `LowDegreeSupport n D`.
- `hcard_le`: hence `Fintype.card (LowDegreeSupport n D) ≤ Fintype.card T`, by
  `Fintype.card_le_of_injective`.
- Then a `calc` chain evaluates `Fintype.card T`: `Fintype.card_sigma` splits it as
  `∑ t : Fin (D + 1), Fintype.card {s // s.card = t.1}`; `Fintype.card_finset_len`
  rewrites each summand as `n.choose t.1`; and `Fin.sum_univ_eq_sum_range` converts the
  `Fin (D + 1)`-sum into a `Finset.range (D + 1)`-sum.

**Remark.** The inequality is only nonstrict because an injection is used in place of an
equivalence; the true value is exactly the binomial sum.
