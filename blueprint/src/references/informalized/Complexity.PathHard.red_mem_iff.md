<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.red_mem_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Path Reduction

**Claim.** Under the stated uniform halting, logarithmic-space, and decision assumptions on $N$, an input belongs to $L$ exactly when its reduction string encodes a path from vertex $0$ to vertex $1$ in the raw graph.

**Proof.** Let $n$ be the number of vertices chosen by the reduction and $s=c_0\ell(|x|)$. The bound on the chosen space parameter follows from $\logSpace(|x|)\le\ell(|x|)$ (`logSpace_le_ell`). If $x\in L$, the code-chain characterization supplies an initial configuration code, a finite chain of valid step codes, an accepting code, and a uniform upper bound on every code (`mem_iff_codeChain`). The exponential vertex bound is large enough that each shifted code $c_i+2$ lies below $n$. In the adjacency word, the initial-code condition gives an edge from $0$ to $c_0+2$, each step gives an edge from $c_i+2$ to $c_{i+1}+2$, and acceptance gives an edge from $c_t+2$ to $1$. The adjacency encoding translates these conditions into raw edges (`rawEdge_adjWordE`); concatenating them gives the required path. The word has the required matrix length and endpoints, using the adjacency-word length formula (`length_adjWordE`).

Conversely, suppose the reduction string encodes a raw path from $0$ to $1$. Equality of the nested pair encodings forces the graph size and endpoints to be those used in the construction; injectivity of pair encoding and of binary words justifies each recovery (`pairEncode_inj`, `bits_injective`). Induct along the path, reading each raw edge as an actual edge of the graph (`rawEdge_adjWordE`). The edge out of vertex $0$ identifies an initial configuration code. Thereafter, an edge into vertex $1$ supplies an accepting code, while an edge between vertices at least $2$ is a step between the corresponding codes. The code-path correctness theorem then implies $x\in L$ (`mem_of_codePath`). Applying this induction to the given path proves the reverse implication.

**Key facts.** `Complexity.PathHard.logSpace_le_ell`, `Complexity.Codec.mem_iff_codeChain`, `Complexity.PathHard.four_le_nV`, `Complexity.PathHard.length_adjWordE`, `Complexity.PathHard.rawEdge_adjWordE`, `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`, `Complexity.Codec.mem_of_codePath`.
