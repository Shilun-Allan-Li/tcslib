<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.binarySign_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# When the Binary Sign Is One

**Claim.** For every $b\in\mathbb{F}_2$, the binary sign of $b$ equals $1$ exactly when $b=0$.

**Proof.** If the sign of $b$ is $1$ and $b$ is nonzero, the two-element field forces $b=1$. The defining character formula then gives the sign as $(-1)^1=-1$, contradicting that it is $1$. Conversely, every additive character sends zero to one, so the sign of zero is one.
