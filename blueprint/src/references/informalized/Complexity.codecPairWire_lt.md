<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecPairWire_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-wire index bound

**Claim.** If the coefficient $D$ is at most $C$, then every pair of a Boolean value and a codec bit has wire index less than $2C(s+n+1)$.

**Proof.** Put $A=C(s+n+1)$. The number of codec bits is at most $A$ by the codec-bit cardinality bound (`Complexity.codecBit_card_le`). Since the equivalence with a finite initial segment assigns each codec bit an index below the number of codec bits, its index is below $A$. If the Boolean component is false, the wire index is just this codec-bit index, hence is below $A$ and therefore below $2A$. If it is true, the index is $A$ plus the codec-bit index, hence below $A+A=2A$.

**Key facts.** `Complexity.codecBit_card_le`.
