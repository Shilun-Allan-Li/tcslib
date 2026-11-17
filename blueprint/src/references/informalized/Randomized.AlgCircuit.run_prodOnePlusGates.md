<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuitExample.lean :: Randomized.AlgCircuit.run_prodOnePlusGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Product Circuit

**Claim.** The execution of the product circuit has value $1$ at index $0$, and value $\prod_{i=0}^{k-1}(1+v_i)$ at index $3k$, where $v_i$ is the evaluation of the $i$th variable-or-one gate on the empty value list.

**Proof.** Induct on $k$. For $k=0$, the circuit has just the constant-one gate, and both asserted values are $1$. For the successor step, let $v_s$ be the values from the circuit at stage $k$. Its length is $3k+1$, by the execution-length formula and the gate-list length formula (`Randomized.AlgCircuit.length_run`, `Randomized.AlgCircuit.length_prodOnePlusGates`). The next three gates append, in order, the factor gate, an addition gate, and a multiplication gate (`Randomized.AlgCircuit.run_append_singleton`). The factor gate evaluates independently of the existing value list, since it is either an input or the constant one. Thus the list grows first to length $3k+2$, with the new factor at index $3k+1$; then to length $3k+3$, with the sum of the old index-$0$ value and the factor at index $3k+2$; and finally to length $3k+4$. The old index-$0$ value remains $1$, and the old index-$3k$ value remains the product from the induction hypothesis. Consequently the final gate multiplies that old product by $1+v_k$, giving the product through $k$ by the finite-product successor identity. The appended-value calculations use the fact that the value appended to a list is found at its former length (`Randomized.AlgCircuit.getD_append_singleton_length`).

**Key facts.** `Randomized.AlgCircuit.length_run`, `Randomized.AlgCircuit.length_prodOnePlusGates`, `Randomized.AlgCircuit.run_append_singleton`, `Randomized.AlgCircuit.getD_append_singleton_length`.
