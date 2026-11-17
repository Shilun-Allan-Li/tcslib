<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.positiveBias_bribeFunction_majority_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bribed Majority Bias Identity

**Claim.** For nonnegative integers $k,m$ and a sign $b\in\{-1,1\}$, the fraction of inputs on which majority is positive after the first $k$ coordinates are set to $b$ equals the fraction of $m$-dimensional sign vectors on which the corresponding threshold is positive.

**Proof.** Unfold positive bias and uniform probability, so both sides are expectations of indicators. The pointwise identity for bribing the first $k$ coordinates (`bribeFunction_majority_head_apply`) identifies the bribed majority at an input $x$ with the threshold function evaluated on the tail component of the split of $x$ into its first $k$ coordinates and its last $m$ coordinates. The tail of a uniformly averaged sign vector is itself uniform: averaging any function of that tail over the full cube gives its average over the $m$-dimensional cube (`expect_majorityCoalitionSplit_tail`). Applying this to the indicator of a positive threshold proves the equality.

**Key facts.** `FABL.bribeFunction_majority_head_apply`, `FABL.expect_majorityCoalitionSplit_tail`.
