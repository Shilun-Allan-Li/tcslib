<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedSums.lean :: BooleanAnalysis.GaussianSpace.evalMultilinearRV_normalizedSumPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Normalized Sum Polynomial

**Claim.** The normalized sum polynomial evaluates on the random variables at any point as their sum divided by $\sqrt n$, with the usual real division convention when $n=0$.

**Proof.** In the defining sum over all subsets, every term indexed by a subset of cardinality other than one vanishes because its coefficient is zero. The remaining subsets are exactly the singletons. Reindexing these singleton terms by their unique elements gives $\sum_{i\in\mathrm{Fin}(n)}(1/\sqrt n)X_i(\omega)$. Factoring out the common coefficient and using $a/\sqrt n=a\,(\sqrt n)^{-1}$ yields the stated expression, including when $n=0$ under the real division convention.
