<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.getD_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded default list lookup

**Claim.** If every entry of a list of natural numbers is at most $1$, then lookup at any index, with default value $0$, is at most $1$.

**Proof.** Express the default lookup using option-valued lookup. If the indexed lookup is absent, the result is the default $0$, which is at most $1$. If it returns an entry $b$, then $b$ belongs to the list; the hypothesis therefore gives $b\leq 1$.
