<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.eval_eq_neg_one_iff_requiredAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation through required signs on the support

**Claim.** A term evaluates to $-1$ exactly when, at every coordinate in its support, the sign vector agrees with the required sign of the literal there.

**Proof.** Suppose first that the term evaluates to $-1$. Fix a coordinate in its support and choose the literal assigned to that coordinate by the construction of $\operatorname{literalAt}$. This literal belongs to the term (FABL.DNFTerm.literalAt_mem), so the characterization of term evaluation (FABL.DNFTerm.eval_eq_neg_one_iff) says that the sign vector matches its required sign. The chosen literal’s coordinate is the specified coordinate (FABL.DNFTerm.literalAt_index), so this is precisely the required-sign condition there. Conversely, suppose the condition holds at every coordinate in the support. For any literal in the term, its coordinate belongs to the support (FABL.DNFTerm.mem_support_of_mem_literals). The support condition gives agreement with the required sign of the literal assigned to that coordinate. The assigned literal equals the original one (FABL.DNFTerm.literalAt_eq), so the original literal is satisfied. Thus every literal is satisfied, and the characterization of term evaluation yields value $-1$.

**Key facts.** `FABL.DNFTerm.eval_eq_neg_one_iff`, `FABL.DNFTerm.literalAt_mem`, `FABL.DNFTerm.literalAt_index`, `FABL.DNFTerm.mem_support_of_mem_literals`, `FABL.DNFTerm.literalAt_eq`.
