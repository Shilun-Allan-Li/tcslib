<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPAmplify.lean :: Randomized.BPP_PTMWith_weakAdv_eq_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak-Advantage BPP Equals BPP

**Claim.** For each fixed exponent parameter, the polynomial-time class with correctness threshold $1/2+\mathrm{weakAdv}(c,n)$ coincides with standard polynomial-time BPP.

**Proof.** Fix the parameter and a language. The proof rewrites membership in the threshold-defined class as membership in the corresponding verifier-based class with that threshold (`mem_BPP_PTMWith_iff`). The weak-advantage characterization theorem says this verifier condition is equivalent to ordinary verifier-based BPP (`inBPPWeak_polyTimeModel_iff_inBPP`). Finally, ordinary verifier-based BPP is equivalent to membership in polynomial-time BPP (`mem_BPP_PTM_iff`). Chaining these equivalences gives the pointwise equality of the two language classes.

**Key facts.** `Randomized.mem_BPP_PTMWith_iff`, `Randomized.inBPPWeak_polyTimeModel_iff_inBPP`, `Randomized.mem_BPP_PTM_iff`.
