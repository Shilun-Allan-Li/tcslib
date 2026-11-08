<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.card_influentialCoordinates_mul_le_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influential-coordinate influence bound

**Claim.** For any Boolean function and real threshold $\tau$, the number of coordinates with influence at least $\tau$, multiplied by $\tau$, is at most the total influence of the associated real-valued function.

**Proof.** Sum the threshold $\tau$ once for each influential coordinate; this sum equals the cardinality of the set times $\tau$. For each such coordinate, membership in the influential-coordinate set says that $\tau$ is at most its Boolean influence. The identity between Boolean influence and the influence of the associated real-valued function (\(\texttt{booleanInfluence\_eq\_influence\_toReal}\)) therefore bounds this sum by the sum of the ordinary influences over those coordinates. Enlarging that sum to all coordinates can only increase it, since every coordinate influence is nonnegative (\(\texttt{influence\_nonneg}\)). The membership characterization used here is that a coordinate belongs to the set exactly when its Boolean influence is at least $\tau$ (\(\texttt{mem\_influentialCoordinates}\)).

**Key facts.** `FABL.mem_influentialCoordinates`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`.
