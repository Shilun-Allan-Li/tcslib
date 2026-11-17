<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean :: CommunicationComplexity.Deterministic.Protocol.nonneg_of_discrepancy_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of a discrepancy bound

**Claim.** If every rectangle has discrepancy in absolute value at most $\gamma$, then $\gamma\ge0$.

**Proof.** The full input space is a rectangle, since it is the product of the full spaces $X$ and $Y$. Applying the assumed bound to this rectangle gives $|\mathrm{disc}_\mu(g,X\times Y)|\le\gamma$. Absolute values are nonnegative, so transitivity yields $0\le\gamma$.
