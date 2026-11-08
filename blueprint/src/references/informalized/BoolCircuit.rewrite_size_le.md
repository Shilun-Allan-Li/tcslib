<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.rewrite_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Size Bound

**Claim.** If $S=n+G$ and $T\le n+G(S+2)$ for natural numbers $n,G,S,T$, then $T\le S(S+2)$.

**Proof.** Substitute $S=n+G$ into the assumed bound. Since $n
e S$ would require $G$ to contribute to $S$, we have $n\le S$; also $G\le S$. Hence $n+G(S+2)\le S+S(S+2)$ is not the needed comparison, but directly using $n=S-G$ gives $n+G(S+2)=S+G(S+1)\le S+S(S+1)=S(S+2)$. Therefore $T\le S(S+2)$.
