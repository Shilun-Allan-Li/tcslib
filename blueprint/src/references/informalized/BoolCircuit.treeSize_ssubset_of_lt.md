<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.treeSize_ssubset_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Inclusion Under a Size Gap

**Claim.** If $(n_0+4)T(n_0)<2^{n_0}$, then the class of Boolean languages recognizable by circuit-tree families of size at most $T(n)$ is a proper subset of the class recognizable with size at most $\max\bigl(T(n),2^{\min(n,n_0)}(\min(n,n_0)+1)+1\bigr)$.

**Proof.** Use the general strict-inclusion result with $\ell(n)=\min(n,n_0)$. Then $\ell(n)\le n$, and each of the two terms whose maximum defines the new size bound is at most that maximum. At $n_0$, $\ell(n_0)=n_0$, so the assumed gap is exactly the required gap for the general result. Substitution gives the stated bound and strict inclusion (\texttt{BoolCircuit.treeSize\_ssubset}).

**Key facts.** `BoolCircuit.treeSize_ssubset`.
