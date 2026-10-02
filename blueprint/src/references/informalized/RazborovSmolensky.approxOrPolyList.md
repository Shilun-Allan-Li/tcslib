<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOrPolyList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The list of all OR-approximating polynomials

**Definition.** `approxOrPolyList p polys` enumerates one OR-approximator per
random seed:

`(Finset.univ : Finset (Fin ℓ → Finset (Fin width))).toList.map (fun S => approxOr p polys S)`.

It is `noncomputable` (it builds `MvPolynomial` values).

**Remark.** It is deliberately a *list* rather than a `Finset` or `Set`: if two
distinct seeds happen to produce the same polynomial, that polynomial appears
twice. Keeping the multiplicity is what makes the length exactly the seed count
`2 ^ (width * ℓ)` (`approxOrPolyList_length`), so that the bad-seed bound
`approxOr_pointwise_bad_count` can be read directly as "at most a `2^{-ℓ}`
fraction of the *entries*" — a de-duplicated collection would break that
correspondence.

**Used in.** `approxOrPolyList_length` and `exists_good_approxOr`, which packages
the list together with its length, its uniform degree bound, and its pointwise
error bound. `approxAndPolyList` is the exact analogue for AND.
