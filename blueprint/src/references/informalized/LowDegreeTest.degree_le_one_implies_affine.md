<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.degree_le_one_implies_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree one implies affine Boolean function

**Claim.** If a Boolean function has degree at most one, then it is linear or its complement is linear; equivalently, it is affine over the Boolean cube.

**Proof.** The degree hypothesis says that every second-order multiplicative derivative of the sign lift equals $1$. The proof first extracts this identity for arbitrary base point and two directions, using the recursive formula for the Gowers product (`gowers_product_succ`). It then evaluates the identity at the zero vector, with directions $x$ and $y$. This yields a constraint on the three Boolean values $f(x)$, $f(y)$, and $f(x\oplus y)$, together with $f(0)$. If $f(0)=0$, the constraint forces $f(x\oplus y)=f(x)\oplus f(y)$ for all $x,y$, so $f$ is linear. If $f(0)=1$, the same constraint shows that the complement $1-f$ satisfies this additivity law, so the complement is linear. These two cases give the asserted alternative.

**Key facts.** `LowDegreeTest.gowers_product_succ`.
