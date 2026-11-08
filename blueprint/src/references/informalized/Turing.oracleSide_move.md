<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleSide_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the indicated side under a move

**Claim.** If $p$ lies on the side of the origin indicated by $b$, then after moving by $d$, the updated tag—changed at the origin according to whether $d$ is non-leftward and otherwise retained—correctly indicates the side of $p+d$.

**Proof.** Separate the case $p=0$ from $p\ne0$. At the origin the marker is present, and checking the three possible moves shows that a negative move lands on the nonpositive side while zero or a positive move lands on the nonnegative side, exactly as the updated tag specifies. Away from the origin the marker is absent, so the tag remains $b$. For each sign of $b$ and each of the three unit moves, the assumed inequality places $p$ strictly on its indicated side; adding the move leaves it there, including a move that reaches the origin. Hence the retained tag describes $p+d$.
