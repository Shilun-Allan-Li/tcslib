<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.exists_dagCircuit_of_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# DAG Simulation of a Sequential Circuit

**Claim.** For every $T\ge1$, a Boolean sequential circuit with $n$ inputs, $r$ registers, and $g$ combinational gates has a DAG circuit on the same inputs that agrees with its output after $T$ steps and has size at most $2((r+g)T+n)$. Well-formedness is preserved, as is well-formedness together with fan-in at most two.

**Proof.** Choose the circuit obtained by unrolling $M$ for $T$ steps. Its evaluation agrees with the sequential run after $T$ steps by the unrolling evaluation theorem (BoolCircuit.SeqCircuit.unroll_eval). The unrolling preserves well-formedness (BoolCircuit.SeqCircuit.unroll_isWellFormed) and preserves the conjunction of well-formedness and fan-in at most two (BoolCircuit.SeqCircuit.unroll_isFaninTwo). Its size is $n+(T+1)M.size$ by the unrolling size formula (BoolCircuit.SeqCircuit.unroll_size). Since $T\ge1$, we have $M.size\le T M.size$, so $n+(T+1)M.size\le n+2T M.size\le 2(n+T M.size)$, which is the required bound.

**Key facts.** `BoolCircuit.SeqCircuit.unroll_eval`, `BoolCircuit.SeqCircuit.unroll_isWellFormed`, `BoolCircuit.SeqCircuit.unroll_isFaninTwo`, `BoolCircuit.SeqCircuit.unroll_size`.
