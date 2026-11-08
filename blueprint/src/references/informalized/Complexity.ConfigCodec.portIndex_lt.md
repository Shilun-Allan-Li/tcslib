<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.ConfigCodec.portIndex_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Port indices lie within range

**Claim.** For every $k$ and every port for $k$ work tapes, its assigned index is strictly less than $3k+7$.

**Proof.** Proceed by the port constructor. The state, input-head, and input-symbol indices are $0,1,2$, which are below $3k+7$. A work-head port indexed by $i<k$ has index $3+i$, below $3+k$. A work-symbol port has index $3+k+2i+t$, where $t$ is either $0$ or $1$; since $i<k$, this is at most $3+k+2(k-1)+1=3k+2$, hence below $3k+7$. A summary port has index $3+3k+t$ with $t\in\{0,1\}$, also below the bound. Finally, the old-bit and new-bit indices are $5+3k$ and $6+3k$, both strictly less than $3k+7$.
