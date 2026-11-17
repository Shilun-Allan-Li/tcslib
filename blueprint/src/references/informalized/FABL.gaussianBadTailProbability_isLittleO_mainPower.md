<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianBadTailProbability_isLittleO_mainPower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian bad-tail little-o bound

**Claim.** For every $\rho\in(0,1)$, as $\mu\to0$ through $(0,1)$, the Gaussian bad-tail probability is little-o of $\mu^{2/(1+\rho)}$.

**Proof.** 1. Set $a=2/(1+\rho)$ and $b=1/\rho^2$. The strict inequality $a<b$ (`mainPower_lt_badTailPower`) lets us choose their midpoint $c=(a+b)/2$, so $a<c<b$. By the soft-power limit (`gaussianBadTailProbability_hasSoftPower`), eventually the logarithmic ratio $\log P_\rho(\mu)/\log\mu$ exceeds $c$. Since $\log\mu<0$, this implies $\log P_\rho(\mu)<c\log\mu$, and hence $P_\rho(\mu)<\mu^c$.

2. Divide by $\mu^a>0$. The bound gives $0\le P_\rho(\mu)/\mu^a\le\mu^{c-a}$ eventually; nonnegativity follows from positivity of the Gaussian upper tail (`standardGaussianUpperTail_pos`). As $\mu\to0$ and $c-a>0$, the right-hand side tends to zero. The squeeze theorem shows that $P_\rho(\mu)/\mu^a$ tends to zero, which is precisely the claimed little-o bound.

**Key facts.** `FABL.mainPower_lt_badTailPower`, `FABL.gaussianBadTailProbability_hasSoftPower`, `FABL.standardGaussianUpperTail_pos`.
