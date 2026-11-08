<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean :: Complexity.PATH_NLComplete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Directed Reachability is NL-Complete

**Claim.** The directed reachability language $\mathrm{PATH}$ belongs to $\mathrm{NL}$, and every language in $\mathrm{NL}$ has a log-space many-one reduction to $\mathrm{PATH}$.

**Proof.** Membership in $\mathrm{NL}$ is supplied directly by `PATH_mem_NL`. For hardness, let $B\in\mathrm{NL}$. The equality `PATH_eq_pathRawLang` identifies the matrix-encoded reachability language with its raw-list encoding. Rewriting the target by this equality allows the established reduction theorem `pathRawLang_NLHard` to give a log-space many-one reduction from $B$ to the target. These membership and hardness statements are precisely the two conditions defining $\mathrm{NL}$-completeness.

**Key facts.** `Complexity.PATH_mem_NL`, `Complexity.PATH_eq_pathRawLang`, `Complexity.pathRawLang_NLHard`.
