<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.half_pow_dnfSwitchingDepth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching-Depth Power Bound

**Claim.** For every real number $\varepsilon>0$, if $d=\lceil\log_2(3/\varepsilon)\rceil$, then $(1/2)^d\le \varepsilon/3$.

**Proof.** Set $q=3/\varepsilon$, which is positive. The ceiling defining $d$ is at least $\log_2 q$, so monotonicity of exponentiation with base $2$ gives $q\le 2^d$. Multiplying by $\varepsilon>0$ yields $3\le\varepsilon 2^d$. Since $2^d>0$, division by $2^d$ gives $3(1/2)^d\le\varepsilon$, and dividing by $3$ proves the result.
