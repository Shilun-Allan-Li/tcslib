<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: Language.not_inSIZE_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Polynomial Circuit Size Bound

**Claim.** For every natural number $c$ and every language of Boolean lists, no family of acyclic Boolean circuits with fan-in at most two recognizes that language while having size at most $n^c$ on inputs of every length $n$.

**Proof.** Assume such a family exists, so in particular its circuit at each input length has size at most $n^c$. Split into the cases $c=0$ and $c>0$. If $c=0$, the size bound at length $2$ is $1$, whereas a circuit on two input bits has size at least $2$ by the definition of size as input count plus gate count. This is impossible. If $c>0$, the bound at length $0$ is $0^c=0$, while every circuit has size at least $1$ (BoolCircuit.DAGCircuit.one_le_size). This too is impossible. Therefore no such family exists.

**Key facts.** `BoolCircuit.DAGCircuit.one_le_size`.
