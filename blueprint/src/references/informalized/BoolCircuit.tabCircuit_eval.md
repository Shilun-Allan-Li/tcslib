<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.tabCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Tabulated Circuit

**Claim.** Under the source-validity and fixed-source-count assumptions, each requested output bit of the tabulated circuit equals the corresponding bit produced by running the program on the concatenation of the fixed bits and the input assignment.

**Proof.** Fix the input assignment and let $P_0$ be the vertex-value list after the preliminary gates. The preliminary-gate evaluation formula (BoolCircuit.runWith_tabPre) identifies this list as the input values followed by the false and true constants, the fixed list $z$, and padding false values. These entries establish the tabulation invariant before any program instructions have been processed: the input and constant positions are correct, the fixed bits are present, and there are no earlier instruction outputs to verify.

Now prove by induction on $i$ that after the gates for the first $i$ instructions have run, the invariant holds. The empty-prefix case is the initialization just described. For the successor step, decompose the gates for the first $i+1$ instructions into those for the first $i$ and those for instruction $i$, using the concatenation law for tabulation gates (BoolCircuit.tabProgGates_append); sequential gate execution respects this decomposition (BoolCircuit.runWith_append). The successor invariant (BoolCircuit.tabInv_succ) applies because instruction $i$ has valid sources and exactly $m$ of them. Hence after all instructions, the invariant says that every output coordinate in the requested block has the value produced by the program.

Finally, the tabulated circuit appends the program gates after its preliminary gates. The same sequential-execution concatenation law identifies its values with the initialized run followed by the full program run. The circuit's output index selects the requested block coordinate, and the final invariant gives exactly the claimed bit.

**Key facts.** `BoolCircuit.runWith_tabPre`, `BoolCircuit.tabProgGates_append`, `BoolCircuit.runWith_append`, `BoolCircuit.tabInv_succ`.
