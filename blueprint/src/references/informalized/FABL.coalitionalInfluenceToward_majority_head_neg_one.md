<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_majority_head_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Influence Toward Minus One

**Claim.** For positive $m$, the influence of the first $k$ coordinates toward $-1$ in majority on $k+m$ coordinates equals the expected upper-tail indicator at threshold $-1/\sqrt{k+m}$ on the full cube, minus the expected upper-tail indicator at the bribe threshold on the remaining $m$ coordinates.

**Proof.** Since majority is monotone (`majority_monotone`), its influence toward $-1$ equals the positive bias of majority minus the positive bias after bribing the head coalition to $-1` (`coalitionalInfluenceToward_neg_one_eq_positiveBias_change`). The bribe-function bias is the expected upper-tail indicator on the remaining $m$ coordinates at the threshold `majorityMinusBribeThreshold k m` (`positiveBias_bribeFunction_majority_head_neg_one`). The unmodified majority bias is the expected upper-tail indicator on the full cube at threshold $-1/\sqrt{k+m}$ (`positiveBias_majority_eq_hammingUpperTail`); its positivity hypothesis holds because $m>0$. Substituting these two expressions gives the claimed difference.

**Key facts.** `FABL.majority_monotone`, `FABL.coalitionalInfluenceToward_neg_one_eq_positiveBias_change`, `FABL.positiveBias_bribeFunction_majority_head_neg_one`, `FABL.positiveBias_majority_eq_hammingUpperTail`.

**Caveat.** The supplied formal statement proves this exact finite-dimensional identity; the informal statement also mentions asymptotic conclusions, which are not part of this declaration.
