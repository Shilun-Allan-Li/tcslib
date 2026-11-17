<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniformLpNorm_le_of_abs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the uniform norm

**Claim.** For a finite set $\Omega$, $q>0$, and functions $f,g:\Omega\to\mathbb R$, if $|f(x)|\le |g(x)|$ at every point, then the uniform $L^q$ norm of $f$ is at most that of $g$.

**Proof.** Unfold the definition of the norm. Since $q>0$, raising nonnegative numbers to the power $q$ preserves their order, so the pointwise hypothesis gives $|f(x)|^q\le |g(x)|^q$. Taking uniform means preserves this inequality. The mean of the terms $|f(x)|^q$ is nonnegative, and the exponent $1/q$ is nonnegative as well; applying the increasing real-power function with this exponent to the inequality between the means proves the result.
