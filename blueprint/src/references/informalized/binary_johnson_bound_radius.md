<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: binary_johnson_bound_radius -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Binary Johnson bound, radius form

**Claim.** If `0 < n`, `1 ≤ d`, `2 * d ≤ n` and `(w : ℝ) ≤ J2 n d`, then
`A0 n d w ≤ 2 * n`, where `A0 n d w` is the maximum cardinality of a code in
`BitVec n` that is admissible for `(n, d, w)`.

**Proof.** Two steps.

1. `refine' A0_le_of_forall_le _` reduces the supremum bound to a bound on
   every individual admissible code.
2. `exact fun C a => binary_johnson_card_bound_of_admissible hn hd1 hd C a hwJ`
   supplies that bound.

**Why it matters.** This is the top-level form of the file: below the Johnson
radius `J2 n d = (n - Real.sqrt (n * (n - 2*d))) / 2`, the extremal
constant-weight code size `A0 n d w` is linear in `n` — a consequence of
Rankin's `2 · dim` bound on unit vectors with pairwise nonpositive inner
products (`rankin_finset_bound`).
