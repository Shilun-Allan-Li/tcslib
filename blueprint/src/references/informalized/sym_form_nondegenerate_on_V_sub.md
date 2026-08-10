<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_nondegenerate_on_V_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Non-degeneracy of the symplectic form on `V_sub M`

**Claim.** Let `M : Finset (Fin n)` and `v : V n p` with `v ∈ V_sub M`. If
`sym_form v w = 0` for every `w ∈ V_sub M`, then `v = 0`. That is, testing only
against vectors supported in `M` already detects non-zero vectors supported in
`M`.

**Proof.**
1. `apply sym_form_nondegenerate v` reduces the goal to `sym_form v w = 0` for
   *every* `w : V n p`, unrestricted.
2. Fix such a `w`. Its restriction `r_E M w` lies in `V_sub M` by construction
   (`(r_E M w).property`), so the hypothesis `h` applies to its coercion, giving
   `sym_form v ↑(r_E M w) = 0`.
3. `sym_form_r_E M v hv w` says `sym_form v w = sym_form v (r_E M w)`, so
   `simpa` with it turns step 2 into `sym_form v w = 0`.

The whole content is that `hv : v ∈ V_sub M` lets an arbitrary test vector be
replaced by its restriction at no cost.

**Used in.** `sym_form_sub_nondegenerate`.
