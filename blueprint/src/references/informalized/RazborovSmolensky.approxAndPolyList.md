<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxAndPolyList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The list of all AND-approximators, one per seed

**Definition.** For `polys : Fin width → MvPolynomial (Fin vars) (ZMod p)`,

`approxAndPolyList p polys = (Finset.univ : Finset (Fin ℓ → Finset (Fin width))).toList.map (approxAnd p polys ·)`.

It materialises the entire seed space — all `2^(width * ℓ)` choices of `ℓ` subsets
of the `width` inputs — as a list of polynomials. A plain definition; no proof.

**Why a list.** It converts the probabilistic statement "a random seed is good for
a fixed input with probability `≥ 1 - 2^(-ℓ)`" into a counting statement over a
finite explicit collection, which is the form `exists_good_approxAnd` exposes: a
list of known length, all of whose entries are low-degree, and for each input at
most a `2^(-ℓ)` fraction of which are wrong. The OR side has the mirror-image
`approxOrPolyList`.

**Used in.** `approxAndPolyList_length` and `exists_good_approxAnd`, both in this
file — no external consumers. The downstream user of the AND approximator,
`exists_gate_poly_family` in `RazborovSmolensky/CircuitDegree.lean`, takes the seed
type `Fin ℓ → Finset (Fin width)` as the `Seed` field of a `GatePolyFamily` and
applies `approxAnd` directly, so the list packaging is presently redundant.
