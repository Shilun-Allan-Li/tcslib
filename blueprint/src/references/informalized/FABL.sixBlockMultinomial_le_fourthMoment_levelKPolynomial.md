<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sixBlockMultinomial_le_fourthMoment_levelKPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Six-Block Multinomial Moment Bound

**Claim.** When $6d\le n$, the multinomial coefficient with six parts of size $d$ and a seventh part of size $n-6d$ is at most the fourth moment of the sum of all degree-$3d$ monomials on the uniform sign cube.

**Proof.** Consider the finite family of choices of six pairwise disjoint coordinate blocks, each of size $d$, and encode each choice as its associated level-$3d$ parity tuple. This encoding is injective (`SixDisjointBlockChoice.toParityTuple_injective`). The general counting-to-moment bound says that any finite family admitting such an injection has cardinality at most the fourth moment of the degree-$3d$ level polynomial (`natCard_le_fourthMoment_levelKPolynomial_of_injective`). Finally, the number of these block choices is the stated six-block multinomial coefficient (`natCard_sixDisjointBlockChoice_eq_multinomial`), giving the desired inequality.

**Key facts.** `FABL.SixDisjointBlockChoice.toParityTuple_injective`, `FABL.natCard_le_fourthMoment_levelKPolynomial_of_injective`, `FABL.natCard_sixDisjointBlockChoice_eq_multinomial`.
