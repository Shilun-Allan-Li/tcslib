<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.one_ninth_lt_distributionalError_of_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distributional Error Lower Bound

**Claim.** For $n\ge 300$, any deterministic one-way protocol for Index with cost at most $n/10$ has distributional error greater than $1/9$ under the stated uniform input distribution.

**Proof.** Fix such a protocol. The small-cost counting bound `badInput_card_ge_half_of_small_cost` shows that at least $2^{n-1}$ of Alice's possible inputs are bad for the protocol. The bad-input error estimate `distributionalError_ge_one_eighth_of_bad_half` then implies that its distributional error is at least $1/8$. Since $1/8>1/9$, the required strict lower bound follows.

**Key facts.** `CommunicationComplexity.Functions.Indexing.badInput_card_ge_half_of_small_cost`, `CommunicationComplexity.Functions.Indexing.distributionalError_ge_one_eighth_of_bad_half`.
