<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.fanoutIn_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-out under concatenation

**Claim.** For any two finite gate lists and any vertex, its fan-out in their concatenation is the sum of its fan-outs in the two lists.

**Proof.** Fan-out counts the gates whose argument list contains the given vertex. In a concatenation, each counted gate comes from exactly one of the two lists, so the count splits into the count from the first list plus the count from the second.
