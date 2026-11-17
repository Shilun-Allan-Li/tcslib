<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.indicatorOne_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idempotence of an Indicator

**Claim.** For every set $B$ of $n$-bit Boolean inputs and every input $y$, the square of the indicator $\mathbf{1}_B(y)$ equals the indicator itself.

**Proof.** If $y\in B$, the indicator equals $1$, whose square is $1$. If $y\notin B$, it equals $0$, whose square is $0$. Thus its square agrees with the indicator in both cases.
