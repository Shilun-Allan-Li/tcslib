<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.mean_bribeFunction_majority_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority mean after bribing the first coordinates

**Claim.** For $k,m\geq0$ and a sign $b$, the mean of majority on $k+m$ coordinates after bribing the first $k$ coordinates to $b$ equals the mean on the remaining $m$ coordinates of the threshold sign of $kb$ plus their sum.

**Proof.** Split an input of length $k+m$ into its first $k$ and last $m$ coordinates. After bribing the first block to $b$, its contribution to the sum defining majority is $k$ times the real value of $b$, while the remaining contribution is the sum over the tail. Thus the bribed majority equals the stated majority-after-head-bribe function evaluated at the tail ($\texttt{FABL.bribeFunction_majority_head_apply}$). Under the uniform distribution on the full cube, that tail is itself uniform on the $m$-dimensional sign cube, so averaging a function of the tail alone gives its uniform mean ($\texttt{FABL.expect_majorityCoalitionSplit_tail}$). Combining these observations proves the equality.

**Key facts.** `FABL.bribeFunction_majority_head_apply`, `FABL.expect_majorityCoalitionSplit_tail`.
