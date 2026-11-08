<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.exists_straightLine_of_dagCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straight-line simulation of fan-in-two circuits

**Claim.** If $n>0$ and a Boolean function on $n$ inputs is computed by a fan-in-two directed acyclic circuit of size at most $S$, then it is computed by a valid straight-line program of length at most $2(S-n)+1$.

**Proof.** Choose a circuit $C$ witnessing the hypothesis. The construction that converts a fan-in-two circuit to a straight-line program, using input vertex $0$ as its designated starting input, gives a valid program whose evaluation agrees with $C$ (`toStraightLine_eval`). Its length is at most $2|E|+1$, where $|E|$ is the number of gates (`toStraightLine_length_le`). Since the circuit size is $n+|E|$ and is at most $S$, we have $|E|\le S-n$. Substituting this into the length bound gives $2(S-n)+1$. The circuit computes the target function, so the constructed program does as well.

**Key facts.** `BoolCircuit.DAGCircuit.toStraightLine_eval`, `BoolCircuit.DAGCircuit.toStraightLine_length_le`.
