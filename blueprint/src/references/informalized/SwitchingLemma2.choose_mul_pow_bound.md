<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: choose_mul_pow_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Trading d binomial steps for a factor (5s)^d

**Claim.** For naturals `n, s, d` with `5 * s ≤ n` and `d ≤ s`,
`n.choose (s - d) * (4 * n) ^ d ≤ n.choose s * (5 * s) ^ d`.

**Proof.** Induction on `d` (`induction d with`).

1. `zero`: both sides collapse to `n.choose s` — `norm_num`.
2. `succ d`: the single-step inequality
   `n.choose (s - d - 1) * (4 * n) ≤ n.choose (s - d) * (5 * s)`. Writing
   `m := s - d - 1` so that `s - d = m + 1`, `Nat.choose_succ_right_eq n m` relates
   the two binomials, `Nat.choose_pos h_mn` gives positivity, and
   `Nat.sub_add_cancel h_mn` gives `(n - m) + m = n`. It suffices that
   `4 * n * (m + 1) ≤ (n - m) * (5 * s)`; after `zify [h_mn]` (to escape truncated
   subtraction) `nlinarith` closes it from `hs : 5 * s ≤ n` and `m + 1 + d = s`.
3. Combine: the induction hypothesis at `d` (via `Nat.le_of_succ_le hd`),
   `Nat.sub_sub` to normalise `s - d - 1`, `pow_succ'` to peel one factor off each
   power, and `nlinarith [pow_pos (show 0 < 4 * n) d]` to multiply the two
   inequalities. ∎

**Used in.** `switching_lemma` (line 1697), where it converts the binomial
`n.choose (s - d)` coming out of `bad_count_bound` into the `numSRestrictions n s`
form with the `(10 * s * w) ^ d` factor.
