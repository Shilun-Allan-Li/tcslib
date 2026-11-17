<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/MistakeBounds/WeightedMajority.lean :: wm_combined_potential_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic potential comparison

**Claim.** If $\beta>0$ and $\beta^{M^*}\le n((1+\beta)/2)^{M_{\mathrm{WM}}}$, then the natural logarithm of the left-hand quantity is at most the natural logarithm of the right-hand quantity.

**Proof.** Both quantities inside the logarithms are positive: $\beta^{M^*}>0$, and $n((1+\beta)/2)^{M_{\mathrm{WM}}}>0$ since $n>0$ and $\beta>0$. The natural logarithm is increasing on the positive reals, so applying it to the assumed inequality preserves the order and gives the conclusion.
