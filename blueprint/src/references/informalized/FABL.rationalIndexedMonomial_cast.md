<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.rationalIndexedMonomial_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed monomial cast

**Claim.** The rational product of the signs indexed by $S$, viewed in $\mathbb R$, equals their real indexed monomial.

**Proof.** For each $i\in S$, the rational factor is the sign $x(i)$ cast from the integers to the rationals, and its real cast equals the real value of that sign. Since the rational-to-real map preserves finite products, casting the product gives exactly the product of the real sign values over $S$.
