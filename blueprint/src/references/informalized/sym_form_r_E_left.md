<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_r_E_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restricting the left argument, against a vector supported in `M`

**Claim.** For `M : Finset (Fin n)`, `s v : V n p` with `v ∈ V_sub M`,
`sym_form (r_E_V M s) v = sym_form s v`. Here `r_E_V M` is the restriction map
`r_E M` composed with the inclusion `(V_sub M).subtype`, so it is an
endomorphism of `V n p` rather than a map into the subspace.

**Proof.** The right-argument version is already available; the left-argument
version follows by antisymmetry.

1. `simpa [r_E_V] using (sym_form_r_E M v hv s).symm` gives
   `sym_form v (r_E_V M s) = sym_form v s`.
2. A `calc` chain then computes
   `sym_form (r_E_V M s) v = - sym_form v (r_E_V M s)` by `sym_form_swap`,
3. `= - sym_form v s` by step 1 (`simp [h_right]`),
4. `= sym_form s v` by `congrArg Neg.neg (sym_form_swap v s)`.

**Anomaly.** This lemma states exactly the same fact as
`sym_form_left_restrict` (same signature, different proof), and it has no
consumers anywhere in TCSlib — `orth_inter_eq_orth_map` uses the
`sym_form_left_restrict` copy instead. It is dead code.
