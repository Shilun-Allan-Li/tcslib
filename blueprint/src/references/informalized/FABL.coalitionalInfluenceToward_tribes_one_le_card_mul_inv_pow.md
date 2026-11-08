<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_tribes_one_le_card_mul_inv_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes Influence Upper Bound

**Claim.** For positive block width $w$, the coalitional influence of the tribes function toward $+1$ on any coordinate set $J$ is at most $|J|2^{-w}$.

**Proof.** The tribes function is monotone (`tribes_monotone`), so its influence toward $+1$ is half the increase in mean after setting the coordinates in $J$ to $+1` (`coalitionalInfluenceToward_one_eq_mean_change`). The mean increase is at most $2|J|2^{-w}$ when $w>0$ (`mean_bribeFunction_tribes_one_sub_mean_le`). Dividing this bound by two gives the stated inequality.

**Key facts.** `FABL.tribes_monotone`, `FABL.coalitionalInfluenceToward_one_eq_mean_change`, `FABL.mean_bribeFunction_tribes_one_sub_mean_le`.
