<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.condMutualInfo_le_condEntropy_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound by the first conditional entropy

**Claim.** The conditional mutual information satisfies $I[X:Y\mid Z;\mu]\le H[X\mid Z;\mu]$.

**Proof.** Use the conditional mutual information identity expressing it as $H[X\mid Z;\mu]-H[X\mid(Y,Z);\mu]$. Conditional entropy is nonnegative, so the subtracted term is at least zero. The claimed upper bound follows.
