<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.hastadThreeSatDegree_tail_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-SAT degree tail bound

**Claim.** For every $\delta\in(0,1/8)$, the degree selected by the three-SAT degree definition satisfies $\sqrt{(1-4\delta)^d}<4\delta$.

**Proof.** The degree is chosen so that $(1-4\delta)^d<(4\delta)^2$. Also $1-4\delta>0$ follows from $\delta<1/8$. For a positive left-hand base, the square-root inequality is equivalent to this strict squared inequality; taking square roots yields the claim.
