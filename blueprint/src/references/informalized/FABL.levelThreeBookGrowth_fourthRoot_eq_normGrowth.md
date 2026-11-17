<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.levelThreeBookGrowth_fourthRoot_eq_normGrowth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth root of level-three growth

**Claim.** For every positive integer $d$, the fourth root of $(3d)^{-2}9^{3d}$ equals $(3d)^{-1/2}(\sqrt3)^{3d}$.

**Proof.** Put $k=3d$, which is positive. The fourth root of $k^{-2}$ is $k^{-1/2}$: rewrite the reciprocal as a negative real power and multiply exponents. For the other factor, write $9=3^2$; raising $9^{3d}$ to the one-fourth power gives $3^{(3d)/2}=(\sqrt3)^{3d}$. Since both factors are nonnegative, the fourth root of their product is the product of their fourth roots. Combining these identities proves the formula.
