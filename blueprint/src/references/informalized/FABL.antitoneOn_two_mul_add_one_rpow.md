<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.antitoneOn_two_mul_add_one_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of a Real Power

**Claim.** For $s\le 0$, the function $x\mapsto(2x+1)^s$ is nonincreasing on $[0,\infty)$.

**Proof.** Take $0\le x\le y$. Then $0<2x+1\le 2y+1$. For positive bases, raising to a nonpositive real power reverses the order, so $(2y+1)^s\le(2x+1)^s$. Hence the function is nonincreasing on the stated interval.
