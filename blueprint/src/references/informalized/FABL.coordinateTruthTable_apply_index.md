<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.coordinateTruthTable_apply_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Truth Table Evaluation

**Claim.** For a Boolean string $w$ of length $n$ and a coordinate $j$, the $j$th coordinate truth table evaluated at the index assigned to $w$ equals the sign encoding of the bit $w_j$.

**Proof.** The truth table at index $i$ reads coordinate $j$ from the Boolean string corresponding to $i$, then applies the Boolean-to-sign encoding. At the index assigned to $w$, the inverse of the indexing equivalence returns $w$ itself. Therefore the value is the sign encoding of $w_j$.
