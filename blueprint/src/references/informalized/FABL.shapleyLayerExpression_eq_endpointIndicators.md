<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyLayerExpression_eq_endpointIndicators -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Endpoint Identity for Layer Weights

**Claim.** For a subset $A$ of an $n$-element ground set, the stated linear combination of its layer weights is $1$ when $A$ is the whole set, $-1$ when $A$ is empty, and $0$ otherwise.

**Proof.** Write $k=|A|$, so $k\le n$. If $n=0$, then $A$ is empty and also the whole ground set; direct substitution gives zero on both sides. Suppose henceforth that $n>0$. If $k=0$, then $A=\varnothing$. Substituting the weights at cardinalities $0$ and $1$ and simplifying gives $-1$, as required. If $k=n$, then $A$ is the whole ground set. Using $\binom{n}{n}=1$ and $\binom{n}{n-1}=n$ in the weights gives $1$. In the remaining case, $0<k<n$, so $A$ is neither endpoint and the right side is zero. The adjacent binomial-coefficient identities give $\binom{n}{k}k=\binom{n}{k-1}(n-k+1)$ and $\binom{n}{k+1}(k+1)=\binom{n}{k}(n-k)$. After dividing by the nonzero layer denominators, these yield $k w(n,k-1)=(n-k+1)w(n,k)$ and $(n-k)w(n,k+1)=(k+1)w(n,k)$. Substituting these into the left side and collecting terms gives zero.
