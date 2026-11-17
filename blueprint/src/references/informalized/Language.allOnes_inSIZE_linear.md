<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: Language.allOnes_inSIZE_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Size Circuits for All Ones

**Claim.** The language of Boolean strings whose entries are all true is recognized by a family of well-formed acyclic Boolean circuits with fan-in at most two, and the circuit for length $n$ has size at most $2n+1$.

**Proof.** Take the family whose length-$n$ circuit is the conjunction circuit `andAllDAG`. It is well formed and every gate has at most two inputs ( `BoolCircuit.andAllDAG_isFaninTwo`), and its size is at most $2n+1$ ( `BoolCircuit.andAllDAG_size_le`). To identify its language, use the characterization of family-language membership as acceptance by the circuit at the word's length ( `BoolCircuit.DAGCircuitFamily.mem_language_iff`). The evaluation theorem for the conjunction circuit says it accepts precisely when every input coordinate is true ( `BoolCircuit.andAllDAG_eval`). For a list, this coordinatewise condition is equivalent to saying every entry of the list is true: each listed entry occurs at some index, and every index retrieves an entry of the list. Thus the family recognizes exactly the all-ones language.

**Key facts.** `BoolCircuit.andAllDAG_isFaninTwo`, `BoolCircuit.andAllDAG_size_le`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`, `BoolCircuit.andAllDAG_eval`.
