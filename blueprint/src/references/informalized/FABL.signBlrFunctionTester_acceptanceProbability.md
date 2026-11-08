<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.signBlrFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign BLR tester acceptance probability

**Claim.** For any Boolean function $f:\{−1,1\}^n\to\{−1,1\}$, the acceptance probability of the sign BLR tester equals the BLR acceptance probability of its transported binary function.

**Proof.** The tester samples a uniform pair $(x,y)$ of binary cube points and queries $f$ at the sign encodings of $x$, $y$, and $x+y$. By the uniform-seed expectation formula (`pmfExpectation_uniformPMF_eq_expect`), its acceptance probability is the uniform expectation over these pairs of the indicator that the first two answers multiply to the third. The transcript formula (`NonadaptiveFunctionTester.transcript_apply`) identifies the three answers with precisely those three evaluations of $f$. Finally, the equivalence between sign acceptance and binary BLR acceptance (`signBlr_accepts_iff_blrAccepts`) identifies the event in this indicator with $\mathrm{blrAccepts}$ for the transported function. Thus the two expectations, and hence the probabilities, are equal.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.NonadaptiveFunctionTester.transcript_apply`, `FABL.signBlr_accepts_iff_blrAccepts`.
