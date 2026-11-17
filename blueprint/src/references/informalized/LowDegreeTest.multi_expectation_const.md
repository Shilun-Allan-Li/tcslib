<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.multi_expectation_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a constant

**Claim.** The uniform average of a constant $c$ over all $k$-tuples of points in the Boolean hypercube is $c$.

**Proof.** There are $2^n$ points in the hypercube (`BoolFourier.card_hypercube`), so there are $(2^n)^k=2^{nk}$ tuples of $k$ points. Each contributes $c$ to the sum defining the average. Thus the sum is $2^{nk}c$, and dividing by the normalization factor $2^{nk}$ gives $c$.

**Key facts.** `BoolFourier.card_hypercube`.
