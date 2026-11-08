<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.ImplicitlyLogspaceComputable.compQ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guarded composition preserves implicit logspace

**Claim.** If $f$ has polynomially bounded output length and its bit and length index languages are in LOGSPACE, then the guarded composition built from $f$ also has polynomially bounded output length and both of its index languages are in LOGSPACE.

**Proof.** Choose constants $C,e$ witnessing the polynomial output-length bound for $f$. The length estimate for guarded composition shows that its output is bounded by $(2C+3)(|w|+1)^{e+1}$ for every input $w$ (the bound is supplied by `compQ_length_le`). For each of the two index languages of the composed function, the closure result for the corresponding composition language (`comp_mem`) gives LOGSPACE membership, using the original hypotheses on the two index languages and the chosen length bound. Unfolding the guarded definition identifies these composition languages with the true-bit and valid-index languages required in the conclusion.

**Key facts.** `Complexity.compQ_length_le`, `Complexity.comp_mem`.
