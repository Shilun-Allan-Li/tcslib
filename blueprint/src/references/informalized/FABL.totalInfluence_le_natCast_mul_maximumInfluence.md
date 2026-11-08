<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.totalInfluence_le_natCast_mul_maximumInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Influence and Maximum Influence

**Claim.** For every Boolean function on the $n$-dimensional cube, the total influence of its real-valued sign representation is at most $n$ times its maximum coordinate influence.

**Proof.** Rewrite total influence as the sum of the coordinate influences. By the identity relating Boolean influence to the influence of the real-valued sign representation (`FABL.booleanInfluence_eq_influence_toReal`), this sum is the sum of the Boolean influences. Each coordinate influence is at most the maximum influence (`FABL.booleanInfluence_le_maximumInfluence`), so summing these bounds gives at most $n$ copies of the maximum. Since there are $n$ coordinates, this is $n$ times the maximum influence.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_le_maximumInfluence`.
