<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Cutoff.lean :: BooleanAnalysis.GaussianSpace.Invariance.lipschitz_cutoffRamp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cutoff ramp is Lipschitz

**Claim.** For $\eta>0$, the function $r(x)=\max(0,\min(1,(v-x)/\eta))$ is Lipschitz with constant $1/\eta$.

**Proof.** The affine function $x\mapsto(v-x)/\eta$ has slope $-1/\eta$, so the absolute difference between its values at $x$ and $y$ is exactly $|x-y|/\eta$. Taking the minimum with a constant and then the maximum with a constant preserves a Lipschitz bound: each operation is a clamp and cannot increase distances between values. Thus the resulting ramp has Lipschitz constant $1/\eta$.
