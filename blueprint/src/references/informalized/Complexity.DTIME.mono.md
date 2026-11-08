<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/DTIME.lean :: Complexity.DTIME.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Deterministic Time

**Claim.** If $T_1(n)\le T_2(n)$ for every $n$, then $\mathrm{DTIME}(T_1)\subseteq\mathrm{DTIME}(T_2)$.

**Proof.** Take a language in $\mathrm{DTIME}(T_1)$, witnessed by a constant $c$ and a machine deciding it within time $cT_1(n)$. Keep the same machine and constant. For every input $x$, the hypothesis gives $T_1(|x|)\le T_2(|x|)$, hence $cT_1(|x|)\le cT_2(|x|)$. Monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) therefore shows that this machine also decides the language within the required $cT_2$ bound.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`.
