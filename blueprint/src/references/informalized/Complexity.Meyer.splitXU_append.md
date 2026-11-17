<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigmaEXP.lean :: Complexity.Meyer.splitXU_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Encoding of an Appended String

**Claim.** If the length of $u$ is $C(|x|+1)^c$, then splitting $x\mathbin{+\!+}u$ by the polynomial padding rule returns the pair encoding of $x$ and $u$.

**Proof.** The concatenation has length $|x|+C(|x|+1)^c$. The split rule therefore finds the index $|x|$: the polynomial padding equation holds there by the assumed length of $u$ and the defining property of the split search (`solveSplit_self'`). Splitting the concatenation at this index recovers $x$ as its prefix and $u$ as its suffix. Applying the definition of the pair encoding gives the claimed equality.

**Key facts.** `Complexity.Meyer.solveSplit_self'`.
