<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.standardGaussianUpperTail_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian Upper Tail at Zero

**Claim.** The standard Gaussian upper-tail probability at $0$ is $1/2$.

**Proof.** The symmetry identity gives that the upper-tail probability at $-0$ equals one minus the upper-tail probability at $0$. Since $-0=0$, this says the value at zero equals one minus itself. Solving this equation gives $1/2$.

**Key facts.** `FABL.standardGaussianUpperTail_neg`.
