<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: numSRestrictions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The number of restrictions with a given number of free variables

**Definition.** `numSRestrictions (n s : ℕ) : ℕ := n.choose s * 2 ^ (n - s)`.

A closed-form natural number, taking no restriction as input: `n.choose s` ways
to choose which `s` of the `n` coordinates stay free, times `2 ^ (n - s)`
assignments of bits to the remaining fixed coordinates. A plain definition; no
proof.

**Remark.** That this really counts the restrictions with exactly `s` free
variables is a separate fact, proved as `fixedSizeRestrs_card` in
`LMN/SwitchingBernoulli.lean` (`(fixedSizeRestrs n k).card = numSRestrictions n
k`, under `k ≤ n`); the same count appears inside `Switching.lean` as
`card_filter_numFree_eq`. Note `Nat` subtraction truncates, so for `s > n` both
factors degenerate and the value is `0` — the correct count in that regime too.

**Used in.** The normalizing denominator of the main results in
`Switching.lean`: `switching_lemma` bounds the number of bad `s`-restrictions by
`numSRestrictions n s * (10 * s * w) ^ d / n ^ d` (stated multiplicatively), and
the CNF-conversion corollary at `(10 * s * w) ^ w`. In both proofs the
definition is unfolded (`unfold numSRestrictions; ring_nf`) to expose
`n.choose s * 2 ^ (n - s)` for `choose_mul_pow_bound`.
