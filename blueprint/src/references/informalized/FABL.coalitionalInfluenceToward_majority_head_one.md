<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_majority_head_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Influence Toward One

**Claim.** For positive $m$, the influence of the first $k$ coordinates toward $1$ in majority on $k+m$ coordinates equals the expected upper-tail indicator at the bribe threshold on the remaining $m$ coordinates, minus the expected upper-tail indicator at threshold $-1/\sqrt{k+m}$ on the full cube.

**Proof.** Majority is monotone (`majority_monotone`), so its influence toward $1$ is the positive bias after bribing the head coalition to $1$ minus the original positive bias (`coalitionalInfluenceToward_one_eq_positiveBias_change`). The first bias is the expected upper-tail indicator on the remaining $m$ coordinates at threshold `majorityPlusBribeThreshold k m` (`positiveBias_bribeFunction_majority_head_one`). The original bias is the expected upper-tail indicator on the full cube at threshold $-1/\sqrt{k+m}$ (`positiveBias_majority_eq_hammingUpperTail`), applicable since $m>0$. Substitution yields the identity.

**Key facts.** `FABL.majority_monotone`, `FABL.coalitionalInfluenceToward_one_eq_positiveBias_change`, `FABL.positiveBias_bribeFunction_majority_head_one`, `FABL.positiveBias_majority_eq_hammingUpperTail`.

**Caveat.** The supplied formal statement proves this exact finite-dimensional identity; the informal statement also mentions asymptotic conclusions, which are not part of this declaration.
