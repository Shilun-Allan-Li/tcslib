<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.ProbabilityDensity.IsBiased.uniformPushforward_comp_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Pushforward Under Reindexing

**Claim.** If the distribution on the Boolean cube induced by a uniform element of \(\Omega\) is \(\varepsilon\)-biased, then composing the map with any bijection from another finite nonempty set preserves that bias bound.

**Proof.** Use the characterization of bias by bounds on expectations of nontrivial Walsh characters (\texttt{FABL.ProbabilityDensity.isBiased\_iff\_expectation}). For a fixed nonzero frequency, the expectation under the uniform pushforward of \(g\circ e\) is the uniform average over \(\Omega'\) of that character evaluated at \(g(e(i))\) (\texttt{FABL.ProbabilityDensity.expectation\_uniformPushforward}). Reindexing this finite average along the bijection \(e:\Omega'\simeq\Omega\) gives exactly the average over \(\Omega\) for the pushforward of \(g\). Its absolute value is at most \(\varepsilon\) by the assumed bias bound, so the characterization gives the claim.

**Key facts.** `FABL.ProbabilityDensity.isBiased_iff_expectation`, `FABL.ProbabilityDensity.expectation_uniformPushforward`.
