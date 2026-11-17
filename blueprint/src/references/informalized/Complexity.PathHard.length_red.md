<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.length_red -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction Output Length

**Claim.** For every machine, parameter $c_0$, and input $x$, the reduction output has length exactly $2N^2+2N+7$, where $N$ is the number of vertices used by the reduction on $x$.

**Proof.** Write $N=nV(codeK(N),c_0,|x|)$. The adjacency word has length $N^2$ by `length_adjWordE`. The innermost encoding of the two fixed indices $0$ and $1$ has length $2N^2+6$, using the pair-encoding length formula (`Turing.length_pairEncode`) and the binary words for $0$ and $1$. Encoding this word together with the adjacency word adds $2N^2+2$ more bits, and the outer encoding with a unary word of length $N$ adds $2N+2$. Combining these contributions gives $2N^2+2N+7$.

**Key facts.** `Complexity.PathHard.length_adjWordE`, `Turing.length_pairEncode`.
