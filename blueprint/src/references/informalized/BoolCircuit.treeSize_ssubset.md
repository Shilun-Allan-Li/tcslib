<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.treeSize_ssubset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Inclusion of Tree Size Classes

**Claim.** Under the stated pointwise bounds on $\ell,T,T'$ and the size gap at $n_0$, the class of Boolean languages recognizable by circuit-tree families of size at most $T(n)$ is a proper subset of the class recognizable with size at most $T'(n)$.

**Proof.** First, every language recognizable within size bound $T$ is recognizable within $T'$, since $T(n)\le T'(n)$ at each input length; this is monotonicity of tree-size recognition (\texttt{Language.InTreeSize.mono}). For strictness, the gap $(\ell(n_0)+4)T(n_0)<2^{\ell(n_0)}$ gives a Boolean function on $\ell(n_0)$ input bits that no circuit tree of size at most $T(n_0)$ computes (\texttt{BoolCircuit.exists\_not\_eval\_of\_lt}). Use these hard functions, length by length, to form the padded language. The upper bound $2^{\ell(n)}(\ell(n)+1)+1\le T'(n)$ ensures this language is recognizable within $T'$ (\texttt{BoolCircuit.padLanguage\_inTreeSize}). The hard function at length $n_0$ ensures it is not recognizable within $T$ (\texttt{BoolCircuit.padLanguage\_not\_inTreeSize}). Thus the inclusion is proper.

**Key facts.** `Language.InTreeSize.mono`, `BoolCircuit.exists_not_eval_of_lt`, `BoolCircuit.padLanguage_inTreeSize`, `BoolCircuit.padLanguage_not_inTreeSize`.
