<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.uniform_expect_prod_le_prod_sqrt_expect_sq_twoRegular_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Coordinate Product Expectation Bound

**Claim.** For finite coordinate set $E$, if each coordinate belongs to exactly two dependency sets, then the uniform expectation of the product of nonnegative functions depending on those sets is at most the product of their root-mean-square values.

**Proof.** Enumerate the finite coordinate set $E$ by a finite ordinal and transport each dependency set and function along this bijection. The transported functions remain nonnegative, and dependence on a dependency set is preserved under the reindexing. Each enumerated coordinate still belongs to exactly two transported dependency sets. The two-regular product expectation bound for finite-ordinal coordinates therefore applies ($\texttt{uniform_expect_prod_le_prod_sqrt_expect_sq_twoRegular}$). Finally, the coordinate bijection induces a bijection between assignments, preserving uniform expectations; this identifies both sides of that bound with the original expectations over $E$.

**Key facts.** `FABL.uniform_expect_prod_le_prod_sqrt_expect_sq_twoRegular`.
