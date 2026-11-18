# Suggested next M1 path

This is a dependency/reuse suggestion for the lead, not additional implementation
scope or a claim of completed proofs. All current snippets are unelaborated and no
Lean/Lake/source edit was performed by the preparers.

1. Fill/check the six weighted wrappers directly from Mathlib's generic support-degree
   API, then the public/private specializations (Degree: 24 candidates staged). Do not
   rederive the generic support/induction arguments described by the old sketches.
2. In parallel with that conceptual work, selection/packing/oneFlag correctness has
   eight short candidates using only existing readers/public API. These have no
   unresolved nonreader prerequisites and can provide small independent proof steps.
3. Fill/check the seven Bucket candidates, then the deterministic SparseFactor list /
   matrix reconstruction obligations using existing List.finRange and Matrix.mul_apply.
4. Prove corr_zero_of_not_bad via `MvPolynomial.eval₂Hom_congr'` on the representation's
   variable set, its Boolean evaluation field and cast compatibility. Together with
   Bucket support/cardinality and SparseFactor reconstruction, this proves
   oneSd_factors_mul and correctionPoly_eval_oneSd.
5. In Polys, the correction polynomial's degree bound is the simpler algebraic branch:
   optional position cases, finite sums of products of two private coordinates, and
   zero public weight. Reuse the proved Degree C/X/sum/product bounds.
6. Prove monomialSlot's combined support bound and halfForm degree bounds, then
   prgPoly_degrees. Tensor halfForm_eval must reuse `Finset.prod_univ_sum` and existing
   MvPolynomial evaluation-map/rename/constant/variable lemmas; do not reprove expansion.
7. Only after prgPoly_degrees and correctionPoly_degrees are actually proved, use the
   two staged combination candidates for G3_degrees and G4_degrees.
8. Finish good-output G1, correction G2, flag-precomputation G3 evaluation, and G4's
   selected-instance sum. Reuse eval_rename, explicit coordinate cancellation, and
   `Finset.sum_eq_single` / sum-ite APIs. Selection is deterministic, including no
   success at kappa=0; no independence or asymptotic argument belongs here.
9. Lift deterministic core correctness through exact draw and existing AllOutputs
   readers/combinators to G4_eval_eq/eval'_correct. `jls_hasComplexity` then chooses
   actual G4, applies its bidegree theorem and the sampled-seed equality.

Existing review notes `polys-notes.txt` and `correctness-notes.txt` record the source
p.16/p.17 mapping and earlier text searches. The follow-up Degree notes now identify
precise generic public counterparts that supersede any suggestion to reproduce
support or finite-set induction calculus. The lead must still run and record the
required exact?/apply? overlap probes before filling genuinely new mathematical glue.
