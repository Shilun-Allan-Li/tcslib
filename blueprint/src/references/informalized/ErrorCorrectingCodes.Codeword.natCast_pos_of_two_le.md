<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: natCast_pos_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An alphabet size at least two is positive as a real

**Claim.** For `q : ℕ` with `2 ≤ q`, the cast `(q : ℝ)` satisfies `0 < (q : ℝ)`.

**Proof.** One line: `exact_mod_cast lt_of_lt_of_le zero_lt_two hq`.

- `lt_of_lt_of_le zero_lt_two hq` gives `0 < q` in `ℕ`, chaining `0 < 2` with
  the hypothesis `2 ≤ q`.
- `exact_mod_cast` transports that across the `ℕ → ℝ` coercion.

This is a deliberately granular numeric helper: it exists so that the entropy
and list-decoding files can discharge the positivity side conditions of
`Real.logb`, division by `q`, and `Real.rpow` from the single arithmetic
hypothesis `2 ≤ q` without repeating a cast argument at every call site.

**Used in.** `Entropy.lean` (three call sites, e.g. `hq₂`, `hq'`, `hqpos`) and
`ListDecoding.lean`, where it feeds `lt_one_of_le_one_sub_inv`.
