<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.dnfDAG_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the DNF Circuit

**Claim.** For every natural number $n$ and Boolean function $f$, the size of the constructed DNF circuit is at most $n2^n+2n+1$.

**Proof.** Let $s$ be the number of satisfying assignments of $f$. Each minterm has $n$ leaves, so the sum of their tree costs is $s\,\mathrm{treeCost}(n)$. The satisfying-assignment list has length at most $2^n$, since it is drawn from all assignments (the finite-set filter cardinality bound gives this inequality). The minterm-tree specification (BoolCircuit.minterms_spec) bounds the number of gates added for those trees by that sum, in addition to the $n$ initial negation gates. The final-tree specification (BoolCircuit.dnf_spec) bounds the additional number of gates by $\mathrm{treeCost}(s)$. The tree-cost estimate (BoolCircuit.dnf_cost_le) bounds $s\,\mathrm{treeCost}(n)+\mathrm{treeCost}(s)$ by $n2^n+1$. Adding the $n$ initial gates gives a total gate count at most $n2^n+n+1$; circuit size also counts the $n$ input vertices, yielding $n2^n+2n+1$.

**Key facts.** `BoolCircuit.minterms_spec`, `BoolCircuit.dnf_spec`, `BoolCircuit.length_negInputGates`, `BoolCircuit.dnf_cost_le`.
