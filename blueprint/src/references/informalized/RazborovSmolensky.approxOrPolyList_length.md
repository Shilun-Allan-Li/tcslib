<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOrPolyList_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The OR-approximator list has length `2^(width·ℓ)`

**Claim.** `(approxOrPolyList (p := p) (ℓ := ℓ) polys).length = 2 ^ (width * ℓ)`.

**Proof.** A two-step `calc` after `classical`. Unfolding the definition,
`simp [approxOrPolyList]` reduces the length to
`Fintype.card (Fin ℓ → Finset (Fin width))` — `List.length_map` leaves the length
unchanged and `Finset.length_toList` together with `Finset.card_univ` turns the
enumeration of `univ` into the cardinality of the seed type. That cardinality is
`2 ^ (width * ℓ)` by `approxSeed_card width ℓ`.

**Remark.** The `map` step is where the list-vs-set choice pays off: no
de-duplication occurs, so the length is exactly the number of seeds.

**Used in.** `exists_good_approxOr`, both for the length clause and to rewrite the
`2 ^ (width * ℓ)` bound of `approxOr_pointwise_bad_count` as `Ps.length`.
