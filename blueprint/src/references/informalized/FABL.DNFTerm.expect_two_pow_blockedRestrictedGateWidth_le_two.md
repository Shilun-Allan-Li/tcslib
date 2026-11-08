<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DNFTerm.expect_two_pow_blockedRestrictedGateWidth_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected exponential blocked width bound

**Claim.** For every DNF term and either gate type, the expected value of $2$ raised to its blocked restricted gate width under a $1/2$-random restriction is at most $2$.

**Proof.** Let the depth be the blocked restricted gate width. Its tail probabilities are bounded by $(1/4)^k$ for every $k$ (FABL.DNFTerm.expect_blockedRestrictedGateWidth_failure_le_quarter). Its values are at most the term’s width, and that width is at most the dimension; these bounds follow from the restricted-width estimate (FABL.DNFTerm.restrictedWidthOf_le_width) and the dimension bound (FABL.DNFTerm.width_le_dimension), together with the fact that dividing a natural number by $5$ cannot increase it. The tail-to-moment estimate for a nonnegative integer-valued depth bounded by the dimension says that these tail bounds imply an expected value of $2^{\mathrm{depth}}$ at most $2$ (FABL.expect_two_pow_le_two_of_tail_le_quarter). Applying that estimate gives the result.

**Key facts.** `FABL.DNFTerm.expect_blockedRestrictedGateWidth_failure_le_quarter`, `FABL.DNFTerm.restrictedWidthOf_le_width`, `FABL.DNFTerm.width_le_dimension`, `FABL.expect_two_pow_le_two_of_tail_le_quarter`.

**Caveat.** The supplied informal statement describes a tail bound for restricted width, while the formal theorem and proof establish an expectation bound for the exponential of blocked restricted gate width.
