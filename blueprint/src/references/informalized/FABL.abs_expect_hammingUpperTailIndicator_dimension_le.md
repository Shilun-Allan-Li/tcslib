<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.abs_expect_hammingUpperTailIndicator_dimension_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rademacher Tail Approximation by a Gaussian

**Claim.** For every real threshold and positive dimension, the absolute difference between the normalized Rademacher upper-tail probability and the standard Gaussian upper-tail probability is at most $2C/\sqrt n$, where $C$ is the third-moment Berry–Esseen constant.

**Proof.** Write the positive dimension as $n=m+1$ for some natural number $m$. The successor-dimension tail estimate gives the desired difference bounded by $2C(\sqrt{m+1})^{-1}$ (`abs_expect_hammingUpperTailIndicator_sub_standardGaussianUpperTail_le`). Since $n=m+1$, this is precisely the stated bound.

**Key facts.** `FABL.abs_expect_hammingUpperTailIndicator_sub_standardGaussianUpperTail_le`.
