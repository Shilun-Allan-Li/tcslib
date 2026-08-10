<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: coord_mul_pmOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Coordinatewise product of two sign vectors

**Claim.** For bit vectors `x y : BitVec n` and a coordinate `i : Fin n`, the
product of the `i`-th entries of their `±1` embeddings satisfies
`pmOne x i * pmOne y i = if x i = y i then 1 else -1`. Here `pmOne x` sends a
bit `true` to `-1` and `false` to `1` (`pmOne`).

**Proof.** A four-way case split on the two bits:
`by_cases hx : x i <;> by_cases hy : y i <;> simp [pmOne, hx, hy]`. In each
branch both factors are literals, so `simp` evaluates the product and the `if`
simultaneously.

**Used in.** `inner_pmOne_pmOne`, where summing this identity over all
coordinates turns `⟪pmOne x, pmOne y⟫` into `n - 2 * hdist x y`. This is the
one place the Hamming metric enters the geometric argument, so the lemma is
kept separate despite being a one-line case bash.
