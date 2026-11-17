<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.globallyFilteredLongCodeCSP_optimum_le_of_noInfluentials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Filtered Optimum from No-Influentials Soundness

**Claim.** Under the stated hypotheses, if the CSP optimum is less than $\tau\epsilon/(8q^2)$, then the globally filtered long-code instance has optimum at most $\alpha+\operatorname{error}(\epsilon)+\tau+r^2/M$.

**Proof.** Use the bounded-soundness filtered-instance theorem with decoded lower bound $\tau\epsilon/(8q^2)$. Its required soundness implication follows from the excess-to-optimum estimate for tests with no influential coordinates, which says that any table with acceptance at least $\alpha+\operatorname{error}(\epsilon)+\tau$ forces the CSP optimum to be at least this decoded lower bound. The assumed strict upper bound on the CSP optimum supplies the contradiction hypothesis of the bounded-soundness theorem. Its conclusion is precisely the desired filtered-instance bound.

**Key facts.** `FABL.RegularUniqueGame.globallyFilteredLongCodeCSP_optimum_le_of_boundedSoundness`, `FABL.RegularUniqueGame.excess_mul_epsilon_div_eight_mul_q_sq_le_optimum_of_noInfluentials`.
