<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.deterministicOneWayDistributionalLowerBound_one_ninth_of_large -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Distributional Lower Bound for Indexing

**Claim.** For $n\ge300$, every deterministic one-way protocol for Indexing with cost at most $\lfloor n/10\rfloor$ has distributional error greater than $1/9$.

**Proof.** Fix any such protocol. Its cost satisfies the hypothesis of the established estimate that every protocol of cost at most $\lfloor n/10\rfloor$, for $n\ge300$, has distributional error strictly greater than $1/9$ (CommunicationComplexity.Functions.Indexing.one_ninth_lt_distributionalError_of_cost_le). Applying that estimate to this protocol gives the claim.

**Key facts.** `CommunicationComplexity.Functions.Indexing.one_ninth_lt_distributionalError_of_cost_le`.

**Caveat.** The supplied informal statement describes a different entropy-based argument and does not match the formal theorem. The proof source establishes only the direct application of the stated upstream estimate.
