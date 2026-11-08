<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.prev_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Bound from a Shared Lower Bound

**Claim.** If $a<tS$ and $tS\le i$, where $S=M.k(2T+1)+|\ell|+3$, then $a<i$.

**Proof.** The number $tS$ lies between $a$ and $i$: the first hypothesis gives $a<tS$, and the second gives $tS\le i$. Transitivity of strict and non-strict order therefore yields $a<i$.
