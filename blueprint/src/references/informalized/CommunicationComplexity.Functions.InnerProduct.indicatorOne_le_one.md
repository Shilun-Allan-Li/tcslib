<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.indicatorOne_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Bounded by One

**Claim.** For every set $B$ of $n$-bit Boolean inputs and every input $y$, the indicator $\mathbf{1}_B(y)$ is at most $1$.

**Proof.** If $y\in B$, the indicator equals $1$. If $y\notin B$, it equals $0$. In either case it is at most $1$.
