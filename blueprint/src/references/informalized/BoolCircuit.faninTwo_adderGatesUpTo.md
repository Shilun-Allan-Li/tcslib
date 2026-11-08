<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.faninTwo_adderGatesUpTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in of partial adder circuits

**Claim.** If $3k\le n$ and $i\le k$, every gate in the adder circuit constructed through step $i$ is well formed and has at most two inputs.

**Proof.** Induct on the number of construction steps $i$. At step zero, the circuit consists of two constant gates, which have empty argument lists and satisfy the claim. At a successor step, the gate list is the earlier partial circuit followed by one bit block. A gate in the earlier part satisfies the claim by the induction hypothesis, since the step bound still holds. A gate in the new block satisfies it by the bit-block fan-in result (`faninTwo_bitBlock`): the construction's indices meet its hypotheses. In particular, the carry and accumulator indices lie below the start of the block by `cinIdx_lt` and `accIdx_lt`, and the parameter bounds give the remaining inequalities and distinctness condition. This covers both portions of the appended list.

**Key facts.** `BoolCircuit.faninTwo_bitBlock`, `BoolCircuit.cinIdx_lt`, `BoolCircuit.accIdx_lt`.
