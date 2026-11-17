<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.sqrt_learningConsequencesThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square Root of the Learning Threshold

**Claim.** For positive rational $t$ and rational $0<\varepsilon\le\tfrac12$, set $e=\varepsilon/8$, $d=\lceil t/e\rceil$, and $\tau=(e^2/t^2)(1/9)^d$. Then, as real numbers, $\sqrt\tau=(e/t)(1/3)^d$.

**Proof.** Let $r=(e/t)(1/3)^d$, with all quantities viewed in $\mathbb R$. The internal error $e$ is positive (the fact `learningConsequencesInternalError_pos`), and $t>0$, so $r\ge0$. Expanding the square gives
\[
r^2=\frac{e^2}{t^2}\left((1/3)^d\right)^2
=\frac{e^2}{t^2}(1/9)^d=\tau.
\]
Since $r$ is nonnegative, the nonnegative square root of $r^2$ is $r$, proving the identity.

**Key facts.** `FABL.learningConsequencesInternalError_pos`.
