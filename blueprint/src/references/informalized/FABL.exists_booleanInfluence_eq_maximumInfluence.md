<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.exists_booleanInfluence_eq_maximumInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainment of maximum influence

**Claim.** When $n>0$, some coordinate of a Boolean function on the sign cube has influence equal to the maximum influence among all coordinates.

**Proof.** Each coordinate influence is nonnegative, by the equality between Boolean influence and the influence of the associated real-valued function ($\mathrm{booleanInfluence\_eq\_influence\_toReal}$ and $\mathrm{influence\_nonneg}$). Thus these values can be viewed as nonnegative reals. Since $n>0$, the finite set of coordinates is nonempty. A real-valued function on a nonempty finite set attains its supremum, so choose a coordinate attaining the supremum of these nonnegative influences. Casting that equality back to the reals identifies its influence with the stated maximum.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`.
