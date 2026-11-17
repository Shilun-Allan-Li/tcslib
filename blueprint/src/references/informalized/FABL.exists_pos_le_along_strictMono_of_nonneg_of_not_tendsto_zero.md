<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.exists_pos_le_along_strictMono_of_nonneg_of_not_tendsto_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive subsequence values

**Claim.** If a sequence of nonnegative real numbers does not converge to zero, then some positive threshold is attained or exceeded at infinitely many indices, and those indices can be chosen as a strictly increasing subsequence.

**Proof.** Failure to converge to zero gives a positive tolerance $\eta$ such that, beyond every index $N$, some term has distance at least $\eta$ from zero. Since all terms are nonnegative, this says that term is at least $\eta$. For each $N$, choose such an index and call it $\operatorname{next}(N)$; it satisfies $N\leq\operatorname{next}(N)$ and its term is at least $\eta$. Starting with this choice and then repeatedly choosing beyond the preceding index produces a subsequence: its first index is $\operatorname{next}(0)$, and each later index is chosen beyond the previous one. The resulting map is strictly increasing, and every selected term is at least $\eta$ by the defining property of each choice.
