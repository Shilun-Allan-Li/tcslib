<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.condMutualInfo_le_entropy_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound by the first entropy

**Claim.** The conditional mutual information satisfies $I[X:Y\mid Z;\mu]\le H[X;\mu]$.

**Proof.** First bound the conditional mutual information by the conditional entropy of $X$ given $Z$ (`condMutualInfo_le_condEntropy_left`). Conditional entropy is at most unconditional entropy (`condEntropy_le_entropy`). Chaining these two inequalities gives $I[X:Y\mid Z;\mu]\le H[X;\mu]$.

**Key facts.** `ProbabilityTheory.condMutualInfo_le_condEntropy_left`.
