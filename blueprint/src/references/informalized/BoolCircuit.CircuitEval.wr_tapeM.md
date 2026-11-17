<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.wr_tapeM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adding a marked tape cell

**Claim.** For every finite list m of natural numbers and every natural number j, writing true in cell j of the tape marked at the nonnegative positions corresponding to members of m produces the tape whose marked positions are exactly the members of j placed at the beginning of m.

**Proof.** Compare the two tapes at an arbitrary integer cell $c$. If $c=j$, the update writes `some true`, and $j$ belongs to the new list by its definition. If $c\ne j$, the update leaves the old tape value unchanged. At such a cell, membership of $c$’s natural coordinate in $j::m$ is equivalent to membership in $m$, since the new head element $j$ cannot equal $c$; the nonnegativity condition is unchanged as well. The tape values therefore agree at every cell, proving equality of the tapes.
