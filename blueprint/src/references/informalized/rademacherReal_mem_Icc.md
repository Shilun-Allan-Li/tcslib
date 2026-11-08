<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: rademacherReal_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support of the Rademacher distribution

**Claim.** For the Rademacher distribution $\tfrac12\delta_{-1}+\tfrac12\delta_{+1}$ on $\mathbb R$, almost every sample lies in $[-1,1]$.

**Proof.** The complement of $[-1,1]$ is measurable. Its measure under the Rademacher distribution is the sum of its measures under the two point masses at $-1$ and $1$, each weighted by $1/2$. Neither point lies in that complement, so both point-mass contributions are zero. Thus the complement has measure zero, which is precisely the asserted almost-everywhere containment.
