<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.andAllDAG_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound for the AND Circuit

**Claim.** For every natural number $n$, the size of the circuit formed by combining all $n$ inputs with AND is at most $2n+1$.

**Proof.** The emitted-tree specification bounds the number of gates by the number of initial gates plus the tree cost of the input list (`BoolCircuit.andAllDAG_spec`). Here the initial list is empty and the input list has length $n$, so the gate count is at most $\mathrm{treeCost}(n)$. The tree-cost estimate gives $\mathrm{treeCost}(n)\le n+2$ (`BoolCircuit.treeCost_le`); the proof also unfolds the definition, treating separately $n=0$ and $n>0$, to obtain the stated bound after adding the $n$ input vertices to the gate count. In either case, the resulting size is at most $2n+1$.

**Key facts.** `BoolCircuit.andAllDAG_spec`, `BoolCircuit.treeCost_le`.
