<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: one_sub_pos_of_le_one_sub_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# 1 − p is positive below the radius 1 − 1/q

**Claim.** For reals `q` and `p` with `0 < q` and `p ≤ 1 - 1 / q`, we have
`0 < 1 - p`. As in `lt_one_of_le_one_sub_inv`, `q` is an arbitrary positive
real.

**Proof.** One line:
`exact one_sub_pos_of_lt_one (lt_one_of_le_one_sub_inv hq hp)`.

- The inner call `lt_one_of_le_one_sub_inv hq hp` yields `p < 1`.
- `one_sub_pos_of_lt_one` converts that to `0 < 1 - p`.

Granular helper: a two-lemma composition, packaged so that a caller holding the
list-decoding radius hypothesis `p ≤ 1 - 1/q` can reach the `1 - p` positivity
side condition in one step instead of two.

**Note for reviewers.** No Lean file in the repository currently applies this
lemma; the only reference outside `Basic.lean` is the `\lean{...}` entry in
`blueprint/src/chapter/ErrorCorrectingCodes/Basic.tex`. It is dead as of this
pass — the call sites that could use it (in `Entropy.lean` and
`ListDecoding.lean`) spell out the two-step composition inline instead.
