<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.ball_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of reachable sets

**Claim.** If $L\le L'$, then the set of numbers below $K$ reachable in at most $L$ steps from an initial number below $K$ is contained in the corresponding set for $L'$.

**Proof.** Take any $t$ in the reachable set for $L$. By the membership characterization of the reachable set (\(\texttt{mem_ball}\)), there is a starting number $u<K$ that satisfies the initial condition and from which $t$ can be reached in at most $L$ steps. The monotonicity of bounded walks says that any such walk of length bound $L$ is also a walk of length bound $L'$ when $L\le L'$ (\(\texttt{Complexity.walkLe_mono}\)). The same starting number therefore witnesses that $t$ belongs to the reachable set for $L'$, proving the inclusion.

**Key facts.** `Complexity.LogProg.ISCount.mem_ball`, `Complexity.walkLe_mono`.
