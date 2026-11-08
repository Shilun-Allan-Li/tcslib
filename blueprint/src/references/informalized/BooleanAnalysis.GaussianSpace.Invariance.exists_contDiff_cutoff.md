<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Cutoff.lean :: BooleanAnalysis.GaussianSpace.Invariance.exists_contDiff_cutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Smooth cutoff with derivative bounds

**Claim.** For each natural number $m$, real $u$, and $\eta>0$, there is a $C^{m+1}$ cutoff valued in $[0,1]$, equal to $1$ to the left of $u$ and $0$ from $u+(m+2)\eta$ onward, with the stated bound on its $(m+1)$st derivative.

**Proof.** Set $v=u+(m+2)\eta$ and start with the ramp $\psi(x)=\max(0,\min(1,(v-x)/\eta))$. The ramp is Lipschitz with constant $1/\eta$ (lipschitz_cutoffRamp). Apply the interval-smoothing construction $m+1$ times. Its iterate is $C^{m+1}$ and its $(m+1)$st derivative is bounded by $(1/\eta)(2/\eta)^m$ (intervalSmooth_iterate_bounds). For each $x$, the iterate takes a value of the original ramp at some $y\in[x,x+(m+1)\eta]$ (intervalSmooth_iterate_exists_value). Since the original ramp lies in $[0,1]$ (cutoffRamp_bounds), so does the iterate. If $x\le u$, then $y+\eta\le x+(m+2)\eta\le v$, so the ramp at $y$ is $1$. If $v\le x$, then $y\ge x\ge v$, so it is $0$. Finally, $(1/\eta)(2/\eta)^m=2^m/\eta^{m+1}$, giving the claimed derivative bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.lipschitz_cutoffRamp`, `BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_iterate_bounds`, `BooleanAnalysis.GaussianSpace.Invariance.cutoffRamp_bounds`, `BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_iterate_exists_value`.
