<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.slpGates_acyclic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of the Gate List

**Claim.** If each statement reads only earlier lines, then every gate in the input-negation gates followed by the statement gates reads only vertices preceding that gate.

**Proof.** Proceed by induction on the statement list, removing its final statement in the inductive step. For the empty list, the input-negation gates are acyclic (BoolCircuit.StraightLine.negGates_acyclic). For a nonempty list $ss++[s]$, the prefix $ss$ remains valid: each of its statements still satisfies the same earlier-line condition. The last statement satisfies the condition at position $|ss|$. By induction, the gate list for $ss$ is acyclic, and the gate list for $ss++[s]$ is that list with $s$'s gate appended (BoolCircuit.StraightLine.slpGates_snoc). It remains to check the appended gate's arguments. Each operand of $s$ has associated vertex less than $2n+|ss|$ by the vertex bound for an operand available before that position (BoolCircuit.SLOperand.vertex_lt). The gate for $s$ lists one or both of these operand vertices, so every argument is less than the new gate's position in the required bound. Appending a gate whose arguments satisfy this bound preserves acyclicity (BoolCircuit.GatesAcyclic.snoc).

**Key facts.** `BoolCircuit.StraightLine.negGates_acyclic`, `BoolCircuit.StraightLine.slpGates_snoc`, `BoolCircuit.SLOperand.vertex_lt`, `BoolCircuit.GatesAcyclic.snoc`.
