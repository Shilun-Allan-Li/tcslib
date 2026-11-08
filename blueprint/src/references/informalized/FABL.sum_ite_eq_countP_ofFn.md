<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_ite_eq_countP_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Sum as a Predicate Count

**Claim.** For a predicate $P$ on $\{0,\ldots,q-1\}$, summing its indicator over those indices gives the number of entries satisfying $P$ in the ordered list $0,1,\ldots,q-1$.

**Proof.** Proceed by induction on $q$. For $q=0$, both the sum and the count are zero. For the step from $q$ to $q+1$, separate the index $0$ from the remaining indices. The sum contributes $1$ exactly when $P(0)$ holds, and the remaining sum is the indicator sum for the shifted predicate on indices $1,\ldots,q$. By induction this remaining sum equals the count on the list of shifted indices: that list is obtained by applying the successor map to $0,\ldots,q-1$, so its predicate count is precisely the count of the shifted predicate. Adding the contribution at $0$ gives the count on the full list.
