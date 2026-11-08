<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: log_one_add_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm bounded by its increment

**Claim.** For every real number $u>-1$, the natural logarithm satisfies $\ln(1+u)\le u$.

**Proof.** Since $u>-1$, we have $1+u>0$. The standard inequality $\ln x\le x-1$ for $x>0$, applied to $x=1+u$, gives $\ln(1+u)\le (1+u)-1=u$.
