<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.totalInfluence_tribes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total influence of tribes

**Claim.** For positive block width $w$ and positive number of blocks $s$, the tribes function has total influence $sw\,2^{-(w-1)}(1-2^{-w})^{s-1}$.

**Proof.** Each of the $sw$ coordinates has the same influence, given by the tribes coordinate-influence formula (\texttt{booleanInfluence\_tribes}): $2^{-(w-1)}(1-2^{-w})^{s-1}$. The equality between Boolean pivotal influence and the influence of the real-valued sign representation (\texttt{booleanInfluence\_eq\_influence\_toReal}) lets us use this formula for each summand in total influence. Summing the common value over the $sw$ coordinates gives $sw$ times that value, which is the claimed expression.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_tribes`.
