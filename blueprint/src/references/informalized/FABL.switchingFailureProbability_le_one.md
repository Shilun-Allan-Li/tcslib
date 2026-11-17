<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.switchingFailureProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Switching Failure

**Claim.** If $0\le\delta\le1$, the switching-failure probability is at most $1$.

**Proof.** Expand the probability as a sum over coordinate sets $J$, with each summand the weight of $J$ times the average indicator over fixed signs. Each average is at most $1$, since the indicator is pointwise at most $1$ (\texttt{switchingFailureIndicator\_le\_one}). The weights are nonnegative under $0\le\delta\le1$ (\texttt{deltaRandomSubsetWeight\_nonneg}), so replacing each average by $1$ can only increase the sum. The resulting sum is the total weight of all coordinate sets, which equals $1$ (\texttt{sum\_deltaRandomSubsetWeight}).

**Key facts.** `FABL.switchingFailureIndicator_le_one`, `FABL.deltaRandomSubsetWeight_nonneg`, `FABL.sum_deltaRandomSubsetWeight`.
