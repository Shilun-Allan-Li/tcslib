<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleSide_distance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed distance from the origin

**Claim.** If $p$ lies on the side indicated by $side$, then $p$ equals the sign prescribed by $side$ times the absolute value of $p$.

**Proof.** If $side$ is false, the hypothesis gives $p\le 0$, so $|p|=-p$; multiplying this absolute value by $-1$ gives $p$. If $side$ is true, then $0\le p$, so $|p|=p$, and multiplying by $1$ leaves $p$ unchanged.
