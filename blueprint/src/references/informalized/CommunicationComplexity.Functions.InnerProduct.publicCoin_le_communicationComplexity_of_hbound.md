<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.publicCoin_le_communicationComplexity_of_hbound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Public-coin communication lower bound

**Claim.** If $(2^k)\sqrt{1/2^n}<1-2\epsilon$, then every public-coin protocol computing the mod-$2$ inner product with error at most $\epsilon$ has communication complexity greater than $k$.

**Proof.** Apply the public-coin communication lower bound from a discrepancy estimate: if every rectangle has discrepancy at most $\gamma$ and $2^k\gamma<1-2\epsilon$, then the communication complexity exceeds $k$ (\texttt{PublicCoin.lt\_communicationComplexity\_of\_discrepancy\_bound}). For the mod-$2$ inner product under the uniform distribution, every rectangle has absolute discrepancy at most $\sqrt{1/2^n}$ (\texttt{abs\_discrepancy\_le\_of\_isRectangle}). Taking this value as $\gamma$, the assumed inequality supplies the required bound, proving the claim.

**Key facts.** `CommunicationComplexity.PublicCoin.lt_communicationComplexity_of_discrepancy_bound`, `CommunicationComplexity.Functions.InnerProduct.abs_discrepancy_le_of_isRectangle`.
