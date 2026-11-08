<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.BPDecidesInSpace.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Bounded-Error Space

**Claim.** If $N$ satisfies the bounded-error decision conditions with space bound $s$, then it satisfies them with any pointwise larger space bound $s'$.

**Proof.** The bounded-error decision property consists of a space guarantee and a separate halting-and-probability guarantee. The latter is unchanged. For the former, the monotonicity of space usage bounds says that a machine using at most $s(|x|)$ cells also uses at most $s'(|x|)$ cells whenever $s(n)\le s'(n)$ (`Turing.FinNDTM.UsesSpace.mono`). Combining these two parts gives the result.

**Key facts.** `Turing.FinNDTM.UsesSpace.mono`.
