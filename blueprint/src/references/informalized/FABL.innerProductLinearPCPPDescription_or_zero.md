<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductLinearPCPPDescription_or_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of the inner product PCPP

**Claim.** For every natural number $m$, either $m=0$ and no Boolean word of length $2m$ has inner product modulo two equal to $1$, or $m+m$ is positive and a PCPP description exists for words with that property.

**Proof.** Split into the cases $m=0$ and $m\ne 0$. When $m=0$, the zero-length inner product cannot equal $1$ (`not_isInnerProductModTwoOne_zero`), giving the first alternative. When $m\ne 0$, $m$ is positive, hence so is $m+m$. The positive-parameter construction `innerProductLinearPCPPDescription` then supplies a PCPP description, giving the second alternative.

**Key facts.** `FABL.not_isInnerProductModTwoOne_zero`.
