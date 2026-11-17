<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.combine_maxFanin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin of a Combined Circuit

**Claim.** For any gate type and finite list $cs$ of Boolean circuit trees, the maximum fanin of the combined circuit is at most the maximum of $2$ and the largest fanin among the circuits in $cs$, with the largest fanin of an empty list taken to be $0$.

**Proof.** The combined circuit runs the recursive construction with fuel equal to the list length. Apply `combineFuel_maxFanin` at that fuel and list, using that the list length is at most itself. The resulting estimate is the stated bound.

**Key facts.** `BoolCircuit.combineFuel_maxFanin`.
