<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean :: Complexity.LogProg.ISGen.mem_ball_iff_rcode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Reachability Equivalence

**Claim.** Under the stated bound on $K$, membership in the bounded ball of initial codes and walks of at most $K$ steps is equivalent to reachability from the initial configuration code by finitely many encoded transitions.

**Proof.** By the ball membership characterization (`Complexity.LogProg.ISCount.mem_ball`), membership supplies a number $u<K$ satisfying the initial-code condition and a bounded walk from $u$ to $t$. The initial-code characterization (`Complexity.Codec.mem_initLang`) identifies $u$ with the code of the initial configuration. A walk of bounded length then gives reachability by valid encoded steps, using the walk-to-reachability fact (`Complexity.walkLe_reach`); each step of the bounded relation is an encoded transition.

Conversely, induct on a reachability path from the initial code to $t$. Every code on such a path lies below $2^{	ext{codeK}(N)(s+\text{logSpace}(|x|)+1)}$, by the path-code bound (`Complexity.ExpBFS.rcode_lt`); the hypothesis therefore places all path codes below $K$. The path is thus a path in the relation restricted to codes below $K$. Convert it to a walk of some finite length (`Complexity.exists_walkLe`), and shorten that walk to length at most $K$ (`Complexity.walkLe_short`), since both endpoints lie below $K$. The initial code satisfies the initial-code condition by `mem_initLang`, so the ball characterization yields membership.

**Key facts.** `Complexity.LogProg.ISCount.mem_ball`, `Complexity.Codec.mem_initLang`, `Complexity.walkLe_reach`, `Complexity.ExpBFS.rcode_lt`, `Complexity.exists_walkLe`, `Complexity.walkLe_short`.
