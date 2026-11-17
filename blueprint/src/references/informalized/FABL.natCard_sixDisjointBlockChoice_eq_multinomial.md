<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_sixDisjointBlockChoice_eq_multinomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Six Blocks and a Multinomial Coefficient

**Claim.** If $6d\le n$, the number of ways to choose six ordered, pairwise disjoint $d$-element subsets of an $n$-element set is the multinomial coefficient with six parts of size $d$ and one part of size $n-6d$.

**Proof.** First count the choices as the successive product $\prod_{j=0}^{5}\binom{n-jd}{d}$ (`natCard_sixDisjointBlockChoice`). The factorial product identity for successive binomial choices says that this product, multiplied by $(d!)^6(n-6d)!$, equals $n!$ (`prod_choose_sub_mul_factorials`). On the other hand, the multinomial coefficient for six parts of size $d$ and a final part of size $n-6d$ is $n!$ divided by that same factorial product, by the multinomial factorial formula. The multiplying factorial product is positive, so cancellation identifies the successive-choice product with this multinomial coefficient, proving the result.

**Key facts.** `FABL.natCard_sixDisjointBlockChoice`, `FABL.prod_choose_sub_mul_factorials`.
