<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.f₂DotProduct_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dot product of concatenated vectors

**Claim.** For vectors $a,x\in\mathbb{F}_2^n$ and $b,y\in\mathbb{F}_2^m$, the dot product of the concatenations of $a$ with $b$ and $x$ with $y$ is the sum of the dot products of the corresponding parts.

**Proof.** Expand the dot product of the concatenated vectors as a sum over all $n+m$ coordinates. The first $n$ terms are the dot product of $a$ with $x$, and the remaining $m$ terms are the dot product of $b$ with $y$. Adding these two parts gives the claimed identity.
