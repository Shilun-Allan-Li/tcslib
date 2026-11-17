<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.initialRestrictionWidth_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of initial restriction width

**Claim.** For natural numbers $a\leq b$, the initial restriction width at $a$ is at most the initial restriction width at $b$.

**Proof.** The ceiling base-$2$ logarithm is monotone in its argument, and $a+1\leq b+1$. Thus the logarithmic term defining the initial restriction width at $a$ is at most the corresponding term at $b$. Multiplication by the positive coefficient $5$ and addition of the same constant $4$ preserve this inequality.
