<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_r_E -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Pairing against a vector supported in `M` only sees the coordinates in `M`

**Claim.** Let `M : Finset (Fin n)` and let `v : V n p` lie in `V_sub M` (i.e.
`v.1 i = v.2 i = 0` for every `i ∉ M`). Then for every `s : V n p`,
`sym_form v s = sym_form v (r_E M s)`, where `r_E M` is the restriction map
zeroing out all coordinates outside `M`.

**Proof.** Both sides are sums of `v.1 i * s.2 i - v.2 i * s.1 i` over
`Finset.univ`, so `refine' Finset.sum_congr rfl fun i hi => _` reduces to one
coordinate.

1. `by_cases hi' : i ∈ M`. For `i ∈ M` the `if i ∈ M` guards inside `r_E` fire
   positively and the two summands are literally equal
   (`simp_all +decide [r_E]`).
2. For `i ∉ M`, `cases hv i hi'` supplies `v.1 i = 0` and `v.2 i = 0`, so both
   summands are `0` (`zero_mul`, `sub_self`).

A granular helper: it is the one place where membership in `V_sub M` is traded
for insensitivity to `r_E`.

**Used in.** `sym_form_r_E_left` and `sym_form_nondegenerate_on_V_sub`.
