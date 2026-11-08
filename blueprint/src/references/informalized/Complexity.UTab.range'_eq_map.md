<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.range'_eq_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural Ranges as Shifted Lists

**Claim.** The list of $s$ consecutive natural numbers starting at $n$ is the list of the first $n$ natural numbers with $s$ added to each entry.

**Proof.** Apply the standard identity expressing a range with a specified starting point as a map over the ordinary range. With step size one, that map sends each entry $j$ of the first $n$ natural numbers to $s+j$, which is the stated shifted list.
