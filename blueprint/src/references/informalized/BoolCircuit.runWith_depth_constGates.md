<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.runWith_depth_constGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depths of Constant Gates

**Claim.** Executing the constant gates corresponding to a list $l$ from an initial depth list $I$ appends $l.length$ copies of $1$.

**Proof.** Induct on $l$. The empty list adds nothing. If $l$ begins with $b$, its constant gate has no arguments, so its depth is $1$. Execution first appends this depth, then processes the gates corresponding to the tail. The induction hypothesis says that these append one copy of $1$ per remaining entry, giving the required list.

**Key facts.** `BoolCircuit.runWith_cons`.
