<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.exercise9_26_addressing_witness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing function witness bounds

**Claim.** For every positive $m$, the addressing function has total influence at most $m+1$, and every function depending on at most $2^{m-1}$ coordinates has relative Hamming distance at least $1/4$ from it.

**Proof.** The two conclusions are supplied directly by the established addressing-function bounds. The total-influence estimate gives the first conjunct (`totalInfluence_addressingFunction_le`). For any function $g$ satisfying the stated junta condition, the separation theorem gives relative Hamming distance at least $1/4$ (`not_close_addressing_of_isKJunta`); its positivity hypothesis is exactly the assumed $m>0$. Combining these two results yields the pair of claims.

**Key facts.** `FABL.totalInfluence_addressingFunction_le`, `FABL.not_close_addressing_of_isKJunta`.
