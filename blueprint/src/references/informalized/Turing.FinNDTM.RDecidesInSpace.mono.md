<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.RDecidesInSpace.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the space bound

**Claim.** If $s(n)\le s'(n)$ for every input length, then a machine satisfying the one-sided-error decision condition with space bound $s$ also satisfies it with space bound $s'$.

**Proof.** The hypothesis consists of the space-use condition together with the time and probability guarantees. Apply monotonicity of space usage (`Turing.FinNDTM.UsesSpace.mono`) to replace $s$ by the pointwise larger bound $s'$. The time and probability guarantees are unchanged, so the full one-sided-error condition holds with $s'$.

**Key facts.** `Turing.FinNDTM.UsesSpace.mono`.
