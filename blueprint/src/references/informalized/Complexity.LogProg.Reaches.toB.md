<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean :: Complexity.LogProg.Reaches.toB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-position reaching

**Claim.** If $c_0$ reaches $c_1$ relative to $c,r,p$ and $-1\le p\le L$, then it also reaches $c_1$ with the register head at every intermediate time bounded between $-1$ and $L$.

**Proof.** Use the same witnessing time and endpoint equality as in the reaching hypothesis. At each intermediate time, that hypothesis supplies a state and input-head position exhibiting the configuration as the reference configuration with register-head position $p$, and guarantees that the state has no oracle call. Choose $q=p$ in the bounded-reaching condition; the assumed inequalities give $-1\le q\le L$.
