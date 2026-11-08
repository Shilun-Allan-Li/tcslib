<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.positiveBias_majority_eq_hammingUpperTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Bias as an Upper Tail

**Claim.** For positive $n$, the positive bias of majority on the $n$-dimensional sign cube equals the fraction of sign vectors $y$ for which $\sum_{i=1}^n y_i/\sqrt n>-1/\sqrt n$.

**Proof.** Unfold positive bias and uniform probability, reducing the result to equality of the two indicator functions at each sign vector $y$. The pointwise positive-bribe indicator identity (`majorityAfterHeadBribe_one_indicator`), applied with $k=0$ and $m=n$, identifies the indicator that the threshold after bribery is positive with the stated upper-tail indicator. At $k=0$, the bribery threshold is $-1/\sqrt n$; the simplification uses that the real value of the sign $+1$ is $1` (`signValue_one`). Therefore the indicators, and hence their averages, agree.

**Key facts.** `FABL.majorityAfterHeadBribe_one_indicator`, `FABL.signValue_one`.
