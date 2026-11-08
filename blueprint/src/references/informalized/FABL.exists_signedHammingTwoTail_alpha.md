<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.exists_signedHammingTwoTail_alpha -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Gaussian Profile Tail Inequality

**Claim.** There is an $\alpha\in(1/4,1/2)$ for which the Gaussian isoperimetric profile at $\alpha$ is less than twice its value at $1/8$.

**Proof.** Strict concavity of the Gaussian isoperimetric profile on $[0,1]$, applied to the distinct endpoints $0$ and $1/4$ with equal weights, shows that its value at their midpoint $1/8$ strictly exceeds the average of its endpoint values. The profile vanishes at $0$, so this gives $I(1/4)<2I(1/8)$. By continuity at $1/4$, the strict inequality persists throughout some neighborhood of that point. Since $1/4<1/2$, points sufficiently close to and strictly to the right of $1/4$ also lie below $1/2$. Choosing any such point gives the required $\alpha$.

**Key facts.** `FABL.strictConcaveOn_gaussianIsoperimetricReal`, `FABL.continuousOn_gaussianIsoperimetricReal`.
