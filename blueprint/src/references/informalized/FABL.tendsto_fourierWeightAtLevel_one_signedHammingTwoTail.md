<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.tendsto_fourierWeightAtLevel_one_signedHammingTwoTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-level weight of signed tails

**Claim.** For each real threshold $t$, the first-level Fourier weight of the signed Hamming two-tail function in dimension $m+1$ tends to $4\,\varphi(t)^2$ as $m$ tends to infinity.

**Proof.** For every dimension, the first-level weight of the signed two-tail function is four times the first-level weight of the ordinary upper-tail indicator, by `fourierWeightAtLevel_one_signedHammingTwoTail`. Applying this identity in dimension $m+1$ rewrites the sequence as four times the ordinary tail indicator's first-level weight. Proposition 5.25 (`proposition5_25`) states that this latter weight tends to the square of the standard Gaussian density at $t$. Multiplication by the constant four preserves convergence and multiplies the limit by four.

**Key facts.** `FABL.fourierWeightAtLevel_one_signedHammingTwoTail`, `FABL.proposition5_25`.
