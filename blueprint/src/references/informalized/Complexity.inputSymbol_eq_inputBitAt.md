<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.inputSymbol_eq_inputBitAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Input Read as a Boundary-Aware Bit

**Claim.** The symbol read by the input head equals the boundary-aware input symbol at the head position: it is absent at the left or right boundary and otherwise is the bit one place before the head position.

**Proof.** If the head position is $0$, the configuration’s input-read definition gives `none`, and so does the boundary-aware input symbol. Otherwise, the configuration’s position bound ensures that the index one less than the position is at most $|w|$. The input symbol at a position one greater than an index is the list lookup at that index (`inputSymbol_at`); applying this with index one less than the head position identifies the configuration’s read with the boundary-aware lookup.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
