<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitPos_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor split position

**Claim.** Moving right from split position $1+\min(j,|w|)$ gives split position $1+\min(j+1,|w|)$, with the position clamped at the right boundary.

**Proof.** If $j<|w|$, the head is not at the right boundary, so moving right increases its position by one (`moveInputPos_pos_of_ne_right`). Since $j+1\le |w|$, the resulting position is $1+(j+1)=1+\min(j+1,|w|)$. If $j\ge |w|$, the current split position is already the right boundary. A rightward move there stays at that boundary (`moveInputPos_rightBoundary`), and the successor split position is clamped there as well. Hence the identity holds in both cases.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_rightBoundary`.
