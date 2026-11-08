<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.card_ball_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial reachable set has size one

**Claim.** If $u_0<K$ and the initial predicate holds exactly at $u_0$, then the set of numbers reachable in zero steps from an initial number has cardinality $1$.

**Proof.** It suffices to show that the zero-step reachable set is the singleton containing $u_0$. By the membership characterization of the reachable set (\(\texttt{mem_ball}\)), membership of $t$ gives a witness $u<K$ satisfying the initial predicate and a zero-step walk from $u$ to $t$. A zero-step walk means $u=t$. The hypothesis describing the initial predicate then gives $u=u_0$, so $t=u_0$. Conversely, $u_0$ belongs to the set: it is below $K$, satisfies the initial predicate by the same hypothesis, and reaches itself in zero steps. Thus the set is exactly the singleton, whose cardinality is $1$.

**Key facts.** `Complexity.LogProg.ISCount.mem_ball`.
