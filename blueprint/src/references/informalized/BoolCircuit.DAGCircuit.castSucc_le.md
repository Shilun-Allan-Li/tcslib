<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.DAGCircuit.castSucc_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the cast successor index

**Claim.** For every $d$ with $0\le d\le N$, its image under the successor embedding has value at most $N$, where $N$ is the number of gates.

**Proof.** The successor embedding preserves the underlying natural number: the value of $d$ after applying it is still $d$. Since $d$ belongs to the finite range ending at $N$, its value is at most $N$.
