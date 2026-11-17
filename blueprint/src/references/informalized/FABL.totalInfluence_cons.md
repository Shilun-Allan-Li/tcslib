<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityOptimality.lean :: FABL.totalInfluence_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total influence under coordinate restriction

**Claim.** For a Boolean function on the $(n+1)$-dimensional sign cube, its total influence equals the average of the total influences of its two restrictions to the first coordinate, plus the uniform probability that those restrictions disagree.

**Proof.** Express total influence as the sum of the Boolean influences over all coordinates, using the equality between Boolean influence and the influence of the associated real-valued function (FABL.booleanInfluence_eq_influence_toReal). Separate the first coordinate from the remaining coordinates. Its influence is exactly the probability that the two restrictions disagree (FABL.booleanInfluence_zero). For each remaining coordinate, its influence is the average of that coordinate's influences in the two restrictions (FABL.booleanInfluence_succ). Summing these identities over the remaining coordinates gives the average of the two restricted total influences; adding the first-coordinate contribution proves the formula.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_zero`, `FABL.booleanInfluence_succ`.
