<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.EncodedRegularUniqueGamesFamily.longCodeFiniteTransform_reducesGap_of_noInfluentials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Long-code reduction from no-influentials soundness

**Claim.** Given an $(\alpha,\beta)$ Dictator-vs.-No-Influentials test and the stated numerical bounds, the finite long-code transform defines a Karp reduction from the Unique Games gap promise to the target Max-CSP gap promise.

**Proof.** Use the test at dimension $q$ to obtain a boundary whose checks use only the finite predicate family (\texttt{IsDictatorVsNoInfluentialsTest.longCodeTestBoundary}); dictator completeness supplies the coordinate-wise acceptance lower bound required by the reduction theorem. Apply the bounded-soundness reduction theorem (\texttt{longCodeFiniteTransform_reducesGap_of_boundedSoundness}) with soundness threshold $\tau\varepsilon/(8q^2)$. To verify its remaining soundness condition, take any semantic game and long-code table whose value is at least $\alpha+\operatorname{error}(\varepsilon)+\tau$. The no-influentials soundness estimate then bounds the game's optimum below by $\tau\varepsilon/(8q^2)$ (\texttt{RegularUniqueGame.excess_mul_epsilon_div_eight_mul_q_sq_le_optimum_of_noInfluentials}). This establishes the bounded-soundness hypothesis, so the theorem gives the desired promise-preserving Karp reduction.

**Key facts.** `FABL.IsDictatorVsNoInfluentialsTest.longCodeTestBoundary`, `FABL.EncodedRegularUniqueGamesFamily.longCodeFiniteTransform_reducesGap_of_boundedSoundness`, `FABL.RegularUniqueGame.excess_mul_epsilon_div_eight_mul_q_sq_le_optimum_of_noInfluentials`.
