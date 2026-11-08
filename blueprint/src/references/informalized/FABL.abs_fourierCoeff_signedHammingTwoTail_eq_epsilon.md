<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.abs_fourierCoeff_signedHammingTwoTail_eq_epsilon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed-tail singleton coefficient

**Claim.** For each coordinate $i$ in dimension $m+1$, the absolute singleton Fourier coefficient of the signed two-sided Hamming tail equals the signed-tail parameter defined from twice the absolute singleton coefficient of the upper-tail indicator.

**Proof.** The singleton coefficient of the signed two-sided tail is twice the singleton coefficient of the upper-tail indicator (`fourierCoeff_signedHammingTwoTail_singleton`). For any coordinate in dimension $m+1$, the latter coefficient is the same expectation of the upper-tail indicator times the normalized Rademacher sum, divided by $\sqrt{m+1}$ (`fourierCoeff_hammingUpperTailIndicator_singleton`). In particular, it equals the coefficient at coordinate zero. Taking absolute values therefore identifies the original quantity with the defining expression for the signed-tail parameter.

**Key facts.** `FABL.fourierCoeff_signedHammingTwoTail_singleton`, `FABL.fourierCoeff_hammingUpperTailIndicator_singleton`.
