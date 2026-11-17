<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.signType_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for Sign Values

**Claim.** Every sign $s\in\{-1,0,1\}$ satisfies $-1\le s\le 1$.

**Proof.** The sign type has exactly the three values $-1$, $0$, and $1$. In each case, its integer coercion lies between $-1$ and $1$, giving both inequalities.
