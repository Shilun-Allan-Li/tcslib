<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/DirectedWalk.lean :: Randomized.hitProb_chainDigraph_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting Probability on a Chain Digraph

**Claim.** On the chain digraph with vertices $\mathrm{Fin}(n+1)$, the probability of hitting vertex $n$ within $T$ steps from vertex $0$ is at most $(T+1)/2^n$.

**Proof.** The auxiliary estimate bounds the hitting probability from any vertex $i$ by $\mathrm{hitProb}(i)\,2^n\leq2^i+T$ (Randomized.hitProb_chainDigraph_le_aux). Apply it at the initial vertex $0$. Since $2^0=1$, this gives $\mathrm{hitProb}(0)\,2^n\leq T+1$. Dividing by the positive quantity $2^n$ yields the asserted bound.

**Key facts.** `Randomized.hitProb_chainDigraph_le_aux`.
