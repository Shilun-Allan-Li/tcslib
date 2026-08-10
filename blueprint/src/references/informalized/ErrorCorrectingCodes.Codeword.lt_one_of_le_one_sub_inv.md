<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: lt_one_of_le_one_sub_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Below 1 − 1/q means below 1

**Claim.** For reals `q` and `p` with `0 < q` and `p ≤ 1 - 1 / q`, we have
`p < 1`. Note that `q` here is an arbitrary positive *real*, not a cast alphabet
size — call sites supply the cast themselves.

**Proof.**

1. `have h_inv_pos : 0 < 1 / q := one_div_pos.mpr hq` — positivity of the
   reciprocal from positivity of `q`.
2. `linarith` combines `h_inv_pos` with `hp : p ≤ 1 - 1/q` to conclude
   `p ≤ 1 - 1/q < 1`.

The `0 < q` hypothesis is doing real work rather than being hygiene: without it
`1/q` could be negative (or zero, at `q = 0`, by Lean's junk-value convention),
and then `1 - 1/q` would not be below one.

**Used in.** `Entropy.lean` (`hp_lt_one`, `hp_1`) and `ListDecoding.lean`, which
composes it with `natCast_pos_of_two_le hq2` to convert the standard
list-decoding radius hypothesis `p ≤ 1 - 1/q` into `p ≤ 1`.
