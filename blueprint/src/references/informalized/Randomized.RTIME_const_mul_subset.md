<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Randomized.RTIME_const_mul_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorbing a Time-Bound Factor

**Claim.** For every natural number $a$ and time bound $T$, $\mathrm{RTIME}(n\mapsto aT(n))\subseteq\mathrm{RTIME}(T)$.

**Proof.** Suppose $L$ has a randomized decider running within a constant multiple of $n\mapsto aT(n)$. If that constant is $c$, the bound is $c(aT(n))$. By associativity of multiplication this is $(ca)T(n)$, which is a constant multiple of $T(n)$. The same machine and the constant $ca$ therefore witness membership in $\mathrm{RTIME}(T)$.
