<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_sub_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The restricted form evaluates as the ambient form

**Claim.** For `M : Finset (Fin n)` and `x y : ↥(V_sub M)`,
`sym_form_sub M x y = sym_form ↑x ↑y`. Here `sym_form_sub M` is notation for
`symB_sub M`, defined as `symB` composed with the inclusion
`(V_sub M).subtype` in both arguments, so the identity just strips the
restriction.

**Proof.** `rfl` — true by definition of `symB_sub`. It is a deliberately
granular `@[simp]` interface lemma: tagged simp, so any goal phrased in the
restricted bilinear form is automatically pushed down to the ambient
`sym_form` where the coordinate lemmas live.

**Used in.** `sym_form_sub_isRefl` and `dim_orth_inter` explicitly, plus
implicitly (via `simp`) throughout `sym_form_sub_nondegenerate` and
`orth_inter_eq_orth_sub_image`.
