<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.prefixVal_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Formula for Prefix Values

**Claim.** For every Boolean sequence $f$ and natural number $i$, the weighted prefix value below $i+1$ equals the value below $i$ plus $(f(i)).toNat\,2^i$.

**Proof.** This is exactly the recursive defining equation for the prefix value at a successor index, so the two sides agree by definition.
