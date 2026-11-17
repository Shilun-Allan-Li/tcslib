<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.deconst_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value preservation under constant removal

**Claim.** For every input assignment and every original vertex $v<n+|C|$, the value at the shifted vertex in the transformed circuit equals the value at $v$ in the original circuit, with out-of-range list lookups interpreted as false.

**Proof.** Let $V$ be the list of values in the transformed circuit. First evaluate the three prefix gates using the gate-value rule (`DAGCircuit.values_getD_gate`): the first produces $
eg V_0$, the second produces true at index $n+1$, and the third produces false at index $n+2$. The latter two facts follow by evaluating their two-input gates (`DAGGate.eval_pair`). We now use strong induction on the original vertex index $v$. If $v<n$, it is an input, and the input-value rule (`DAGCircuit.values_getD_input`) gives the same assigned value at index $v$ in both circuits; the shift leaves this index unchanged. Otherwise write $v=n+i$. The acyclicity condition ensures that every argument $a$ of original gate $i$ has index below $n+i$, so the induction hypothesis applies to each argument. At index $n+i+3$, the transformed circuit contains the image of gate $i$. The strict-gate evaluation lemma, using the induction hypotheses for its arguments and the established true and false constants, shows that this image has the same value as the original gate (`strictGate_eval`). The gate-value rule identifies these gate evaluations with the corresponding list entries, proving the claim at $v$.

**Key facts.** `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.DAGGate.eval_pair`, `BoolCircuit.DAGCircuit.values_getD_input`, `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.strictGate_eval`.
