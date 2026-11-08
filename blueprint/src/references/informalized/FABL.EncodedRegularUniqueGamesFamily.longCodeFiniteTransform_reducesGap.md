<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.EncodedRegularUniqueGamesFamily.longCodeFiniteTransform_reducesGap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Long-code reduction preserves the gap

**Claim.** Given an $(\alpha,\beta)$ Dictator-vs.-No-Notables test and the stated numerical bounds, the finite long-code transform defines a Karp reduction from the Unique Games gap promise to the target Max-CSP gap promise.

**Proof.** First use the test at dimension $q$ to obtain a boundary: its predicates lie in the finite allowed family (\texttt{IsDictatorVsNoNotablesTest.longCodeTestBoundary}). Its dictator completeness gives acceptance at least $\beta$ for every coordinate. These are precisely the inputs required by the bounded-soundness reduction theorem (\texttt{longCodeFiniteTransform_reducesGap_of_boundedSoundness}). Apply that theorem with soundness threshold $\tau\varepsilon^5/18$. Its remaining soundness hypothesis asks that whenever a long-code table has value at least $\alpha+\operatorname{error}(\varepsilon)+\tau$, the Unique Games optimum is at least this threshold. For each semantic game and such table, the no-notables soundness estimate supplies that optimum lower bound (\texttt{RegularUniqueGame.excess_mul_epsilon_pow_five_div_eighteen_le_optimum}). Thus the bounded-soundness theorem applies and yields the claimed promise-preserving reduction.

**Key facts.** `FABL.IsDictatorVsNoNotablesTest.longCodeTestBoundary`, `FABL.EncodedRegularUniqueGamesFamily.longCodeFiniteTransform_reducesGap_of_boundedSoundness`, `FABL.RegularUniqueGame.excess_mul_epsilon_pow_five_div_eighteen_le_optimum`.
