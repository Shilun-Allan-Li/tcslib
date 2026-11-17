<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.DAGCircuitFamily.HasLogspaceAdjacency.isLogspaceUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency uniformity implies uniformity

**Claim.** A canonical family of Boolean circuits with logspace-decidable adjacency information is logspace-uniform.

**Proof.** Use the adjacency-walk description of the circuit family as the encoding procedure. Its description reproduces the encoding of each circuit on the unary input of the corresponding length (\texttt{descr\_replicate}).

To show that this procedure is implicitly logspace-computable, first bound its output length. The canonical encoding-length estimate (\texttt{length\_encode\_le\_of\_canonical}) bounds the encoding by $4(\mathrm{size}(C_n)+1)^3$. If the family has polynomial size, say $\mathrm{size}(C_n)\le a(n+1)^k$, then $\mathrm{size}(C_n)+1\le(a+1)(n+1)^k$. Consequently the description length is at most $4(a+1)^3(n+1)^{3k}$, giving a polynomial bound.

It remains to decide the description's bits and its length in logspace. The adjacency-walk procedure provides both index languages: with its output-bit parameter set to false, it decides whether a given position is a true bit of the circuit encoding; with that parameter set to true, it decides whether the position lies within the encoding. These are the two logspace languages required for implicit logspace computability (\texttt{walk\_lang}); the canonical-family hypotheses supply its assumptions. The description procedure therefore witnesses logspace uniformity.

**Key facts.** `BoolCircuit.AdjWalk.length_encode_le_of_canonical`, `BoolCircuit.AdjWalk.walk_lang`, `BoolCircuit.AdjWalk.descr_replicate`.
