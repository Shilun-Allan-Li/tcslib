<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.DNFTerm.notFalsified_indicator_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Formula for the Nonfalsification Indicator

**Claim.** The real indicator of the event that a term is not falsified equals the product over all coordinates of the local nonfalsification factors.

**Proof.** Split according to whether the term is not falsified. If it is, every literal is not falsified, by the characterization of a nonfalsified term (`notFalsified_iff`). For each coordinate in the support, the selected literal belongs to the term (`literalAt_mem`), and therefore is not falsified. Its coordinate is the coordinate being considered (`literalAt_index`), so the corresponding local factor is $1$. Coordinates outside the support also have local factor $1$ by definition. Thus every factor in the product is $1$, as is the indicator.

If the term is falsified, some literal in the list is falsified, since the negation of the “no literal is falsified” condition gives such a witness. Its coordinate belongs to the support (`mem_support_of_mem_literals`), and the literal selected at that coordinate is exactly this witness (`literalAt_eq`). Consequently the local factor at that coordinate is $0$. The product over all coordinates is therefore $0$, matching the indicator in this case.

**Key facts.** `FABL.DNFTerm.notFalsified_iff`, `FABL.DNFTerm.literalAt_mem`, `FABL.DNFTerm.literalAt_index`, `FABL.DNFTerm.mem_support_of_mem_literals`, `FABL.DNFTerm.literalAt_eq`.
