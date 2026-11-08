<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.switchingFailureProbability_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching failure at threshold zero

**Claim.** For every sign-valued Boolean function and every real parameter $\delta$, the switching-failure probability at threshold zero equals $1$.

**Proof.** Every decision-tree depth is a natural number, so it is at least zero. Consequently the threshold-zero indicator equals $1$ for every restriction. The probability therefore reduces to the sum of the random-subset weights over all subsets of coordinates, and this sum is $1$ ($\texttt{sum_deltaRandomSubsetWeight}$).

**Key facts.** `FABL.sum_deltaRandomSubsetWeight`.
