<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.expect_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation Commutes with Expectation

**Claim.** The uniform expectation of the pointwise negative of a function is the negative of its uniform expectation.

**Proof.** Apply homogeneity of uniform expectation with scalar $-1$ (BooleanAnalysis.ThresholdFunctions.expect_const_mul). Since $(-1)f(x)=-f(x)$ and $(-1)\mathbb E[f]= -\mathbb E[f]$, this is the desired identity.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_const_mul`.
