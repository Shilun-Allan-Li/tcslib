<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.treeSize_one_ssubset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Inclusion of Tree Size Classes

**Claim.** The class of Boolean languages recognizable by a family of Boolean circuit trees whose size is at most $1$ at every input length is a proper subset of the class recognizable with size at most $\max\bigl(1,2^{\min(n,3)}(\min(n,3)+1)+1\bigr)$ on inputs of length $n$.

**Proof.** Apply the strict-inclusion theorem for a size bound $T$ at a length $n_0$ satisfying $(n_0+4)T(n_0)<2^{n_0}$ (\texttt{BoolCircuit.treeSize\_ssubset\_of\_lt}) with $T(n)=1$ and $n_0=3$. Its hypothesis reduces to $7<8$. The resulting larger bound is $\max(1,2^{\min(n,3)}(\min(n,3)+1)+1)$, as claimed.

**Key facts.** `BoolCircuit.treeSize_ssubset_of_lt`.
