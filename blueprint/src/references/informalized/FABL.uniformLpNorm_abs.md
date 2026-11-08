<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NonnegativeReduction.lean :: FABL.uniformLpNorm_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute-value invariance

**Claim.** For a finite set $\Omega$, a real number $p$, and a function $f:\Omega\to\mathbb R$, the uniform $L^p$ quantity of $x\mapsto |f(x)|$ equals that of $f$.

**Proof.** Unfold the definition: both quantities are the $p^{-1}$ power of the expectation of the pointwise $p$th power of the absolute value. At each $x$, the integrand for the function $|f(x)|$ is $\bigl||f(x)|\bigr|^p$, which equals $|f(x)|^p$ because taking an absolute value twice changes nothing. Hence the expectations, and therefore the resulting quantities, agree.
