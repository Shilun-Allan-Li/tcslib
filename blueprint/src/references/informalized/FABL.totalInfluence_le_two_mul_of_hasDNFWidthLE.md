<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.totalInfluence_le_two_mul_of_hasDNFWidthLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound from DNF Width

**Claim.** If a Boolean function has a DNF representation of width at most $w$, then its total influence is at most $2w$.

**Proof.** Choose a DNF formula of width at most $w$ representing the function. Total influence is twice the expected number of negative-one pivotal coordinates (`FABL.totalInfluence_eq_two_mul_expect_card_negOnePivotal`). At every input, the number of those coordinates is at most the formula's width (`FABL.card_negOnePivotal_le_width`), hence at most $w$. Taking expectations gives an expected count at most $w$, and the identity then gives total influence at most $2w$.

**Key facts.** `FABL.totalInfluence_eq_two_mul_expect_card_negOnePivotal`, `FABL.card_negOnePivotal_le_width`.
