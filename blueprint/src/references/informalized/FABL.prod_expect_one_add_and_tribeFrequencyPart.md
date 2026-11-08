<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.prod_expect_one_add_and_tribeFrequencyPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of Tribe Fourier Expectations

**Claim.** The product of the stated uniform-cube expectations equals the expression determined by the number of nonempty coordinate parts, the total size of $T$, and the parameters $w,s$.

**Proof.** Partition the $s$ indices into those whose part of $T$ is empty and those whose part is nonempty. Write $k$ for the number in the second class. The two classes are disjoint and exhaust the indices, so their sizes are $s-k$ and $k$. The expectation for each empty part is $2(1-2^{-w})$, while for each nonempty part $S$ it is $2\cdot 2^{-w}(-1)^{|S|+1}$; these are the two cases of the single-part expectation formula (`expect_one_add_andFunction_mul_monomial`). Multiplying separately over the two classes gives $[2(1-2^{-w})]^{s-k}$ and $2^k(2^{-w})^k$ times the product of the signs. The parts partition $T$, so their sizes sum to $|T|$ (`card_tribeFrequencyPart_sum`); adding one in the exponent for each of the $k$ nonempty parts makes the total sign exponent $|T|+k$. Finally, $2^{s-k}2^k=2^s$, yielding the claimed expression.

**Key facts.** `FABL.expect_one_add_andFunction_mul_monomial`, `FABL.card_tribeFrequencyPart_sum`.
