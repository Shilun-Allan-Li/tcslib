<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: dim_ineq_aux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Dimension inequality for `S` and its restriction to `M`

**Claim.** For isotropic `S ≤ V n p` (`hS : IsIsotropic S`) and any
`M : Finset (Fin n)`,
`finrank S + finrank (S_M S M) ≤ 2 * M.card + finrank (S_M S (E_c M))`.

**Proof.** One line: `linarith [g_add_dims S hS M]`. The cited identity says
`g S M + finrank (S_M S M) + finrank S = 2 * M.card + finrank (S_M S (E_c M))`,
so the claim is that identity with the nonnegative term `g S M` dropped.

**Remark.** A granular ℕ-arithmetic corollary of `g_add_dims`, recording the
inequality direction that later dimension counts want. It is currently
**unused** — every consumer in the file calls `g_add_dims` directly.
