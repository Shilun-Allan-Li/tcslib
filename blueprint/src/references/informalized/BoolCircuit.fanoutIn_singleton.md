<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.fanoutIn_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-out in a single gate

**Claim.** For any gate $g$ and vertex $v$, the fan-out in the singleton list containing $g$ is one if $g$ reads $v$, and zero otherwise.

**Proof.** The singleton list has exactly one gate. It is counted in the fan-out precisely when $v$ belongs to its argument list, so the count is one in that case and zero otherwise.
