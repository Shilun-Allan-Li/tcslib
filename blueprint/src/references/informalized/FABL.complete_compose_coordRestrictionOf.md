<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.complete_compose_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Coordinate Restrictions

**Claim.** Completing the composition of the restriction determined by $J$ and $z$ with a second coordinate restriction yields, on $J$, the reindexed completion of the second restriction, and off $J$, the fixed signs $z$.

**Proof.** Check equality coordinate by coordinate. If $i\in J$, the combined sign vector at $i$ is its free-coordinate component (`combineSignCube_apply_free`). The first restriction leaves this coordinate free, so composing it with the second restriction gives exactly the second restriction at $i$. Its completion is therefore the completion of the second restriction at the corresponding reindexed coordinate, as on the right-hand side. If $i\notin J$, the combined sign vector is its fixed-coordinate component (`combineSignCube_apply_fixed`). The first restriction fixes this coordinate to $z_i$, and composition preserves that fixed choice regardless of the second restriction. Because a sign is either $1$ or $-1$, the definition of the restriction selects the matching fixed case, giving $z_i$ on both sides.

**Key facts.** `FABL.combineSignCube_apply_free`, `FABL.combineSignCube_apply_fixed`.
