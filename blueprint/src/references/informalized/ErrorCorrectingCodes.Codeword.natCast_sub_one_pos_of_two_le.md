<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: natCast_sub_one_pos_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# q − 1 is positive when q is at least two

**Claim.** For `q : ℕ` with `2 ≤ q`, the real number `(q : ℝ) - 1` satisfies
`0 < (q : ℝ) - 1`. Again the subtraction happens in `ℝ` after the cast, so no
truncation is involved.

**Proof.** One line:
`linarith [show (1 : ℝ) < q from natCast_one_lt_of_two_le hq]`.

- `natCast_one_lt_of_two_le hq` provides `1 < (q : ℝ)`.
- `linarith` rearranges it to `0 < q - 1`.

Granular numeric helper, and the one of the `q - 1` pair that is actually used:
the `q`-ary entropy function `qaryEntropy q p` contains the term
`p * Real.logb q (q - 1)`, whose manipulation requires the argument `q - 1` to be
strictly positive rather than merely nonnegative.

**Used in.** `Entropy.lean` at three call sites (`hq₄`, `hq1_pos`, and the
`Fintype.one_lt_card` application at line 54, where `2 ≤ Fintype.card α` is
obtained via `Nat.succ_le_iff.mpr`).
