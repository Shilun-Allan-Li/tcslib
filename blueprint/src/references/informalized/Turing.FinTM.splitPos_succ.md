<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitPos_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advancing a saturated position

**Claim.** Moving one cell right from the saturated position for $j$ gives the saturated position for $j+1$.

**Proof.** Split on whether $j<|w|$. If so, the position is strictly before the right boundary, so moving right increases its value by one (`moveInputPos_pos_of_ne_right`); the minimum in the definition of the saturated position then gives the position for $j+1$. If $j\ge |w|$, the current position is already the right boundary. Movement there remains at that boundary (`moveInputPos_rightBoundary`), which is also the saturated position for $j+1$.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_rightBoundary`.
