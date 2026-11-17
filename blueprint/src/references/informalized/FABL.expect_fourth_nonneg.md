<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_fourth_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Fourth Moment

**Claim.** For every real-valued function $f$ on the $n$-dimensional sign cube, its uniform fourth moment satisfies $\mathbb E[f^4]\ge 0$.

**Proof.** Write the uniform expectation as the sum of the values divided by the size of the cube. Each summand is a fourth power of a real number and is therefore nonnegative; the divisor is positive. Hence their average is nonnegative.
