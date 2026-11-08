<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSat.lean :: BoolCircuit.mem_cktSat_iff_is3Satisfiable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Satisfiability and 3-SAT

**Claim.** A Boolean circuit tree is satisfiable exactly when the 3-CNF formula obtained by converting its Tseitin encoding to 3-CNF is satisfiable.

**Proof.** First, the circuit-tree satisfiability theorem identifies satisfiability of the circuit with satisfiability of its Tseitin CNF encoding ($\texttt{BoolCircuit.TreeCircuit.satisfiable_iff_isSatisfiable}$). Then the CNF-to-3-CNF equivalence says that a CNF formula is satisfiable exactly when its 3-CNF conversion is satisfiable ($\texttt{SATTo3SAT.SAT_to_3SAT_equivalence}$). Applying this to the circuit's Tseitin encoding and composing the two equivalences proves the result.

**Key facts.** `BoolCircuit.TreeCircuit.satisfiable_iff_isSatisfiable`, `SATTo3SAT.SAT_to_3SAT_equivalence`.
