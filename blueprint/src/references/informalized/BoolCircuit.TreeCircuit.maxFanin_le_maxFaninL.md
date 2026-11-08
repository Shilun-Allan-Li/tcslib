<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit fanin bounded by list maximum

**Claim.** If a circuit $c$ occurs in a list $cs$, then its maximum fanin is at most the maximum fanin aggregated over $cs$.

**Proof.** The proof follows the list membership through a nonempty list. If $c$ is the head, the list maximum is the maximum of the head's fanin and the tail maximum, so it is at least the head's fanin. If $c$ occurs in the tail, induction bounds its fanin by the tail maximum, and the list maximum is at least that tail maximum. In either case its fanin is bounded by the list maximum.
