<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.abs_le_uniformLInfinityNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Uniform Norm Bound

**Claim.** For a finite nonempty set $\Omega$ and $f\colon\Omega\to\mathbb R$, every value $|f(x)|$ is at most the uniform norm of $f$.

**Proof.** By definition, the uniform norm is the supremum of the finitely many values $|f(y)|$ as $y$ ranges over $\Omega$. Since $x\in\Omega$, the defining property of a supremum gives $|f(x)|\leq\max_{y\in\Omega}|f(y)|$.
