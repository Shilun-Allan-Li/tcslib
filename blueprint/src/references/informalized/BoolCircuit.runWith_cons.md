<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution Beginning with One Gate

**Claim.** Executing $g::g_s$ from $I$ gives the same list as executing $g_s$ from $I$ with $f(g,I)$ appended first.

**Proof.** The first step of execution processes $g$ and appends the value $f(g,I)$ to $I$. The remaining gates $g_s$ are then processed from that updated list, which is exactly the stated expression.
