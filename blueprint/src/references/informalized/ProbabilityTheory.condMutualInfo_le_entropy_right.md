<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.condMutualInfo_le_entropy_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional mutual information bound

**Claim.** The conditional mutual information of $X$ and $Y$ given $Z$ is at most the entropy of $Y$.

**Proof.** First, conditional mutual information is bounded by the conditional entropy of its second variable: $I[X:Y\mid Z;\mu]\le H[Y\mid Z;\mu]$ (\texttt{condMutualInfo\_le\_condEntropy\_right}). Next, conditioning cannot increase entropy, so $H[Y\mid Z;\mu]\le H[Y;\mu]$ (\texttt{condEntropy\_le\_entropy}). Transitivity gives the claimed bound.

**Key facts.** `ProbabilityTheory.condMutualInfo_le_condEntropy_right`.
