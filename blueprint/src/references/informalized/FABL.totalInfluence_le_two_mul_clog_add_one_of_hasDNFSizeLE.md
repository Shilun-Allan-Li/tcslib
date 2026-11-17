<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.totalInfluence_le_two_mul_clog_add_one_of_hasDNFSizeLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound from DNF Size

**Claim.** If a Boolean function has a DNF representation with at most $s$ terms, then its total influence is at most $2(\lceil\log_2 s\rceil+1)$, expressed as $2(\operatorname{clog}(2,s)+1)$.

**Proof.** Choose a DNF formula of size at most $s$ representing the function. Total influence equals twice the expected number of negative-one pivotal coordinates (`FABL.totalInfluence_eq_two_mul_expect_card_negOnePivotal`). For each input, the number of such coordinates is at most the selected width of the formula (`FABL.card_negOnePivotal_le_selectedWidth`). Taking expectations preserves this pointwise inequality. The expected selected width is at most $\operatorname{clog}(2,s)+1$ (`FABL.expect_selectedWidth_le_clog_add_one`). Combining these bounds yields the stated estimate.

**Key facts.** `FABL.totalInfluence_eq_two_mul_expect_card_negOnePivotal`, `FABL.card_negOnePivotal_le_selectedWidth`, `FABL.expect_selectedWidth_le_clog_add_one`.
