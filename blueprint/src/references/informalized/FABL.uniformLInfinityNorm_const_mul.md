<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLInfinityNorm_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling the supremum norm

**Claim.** For a finite nonempty set $\Omega$, a real number $c$, and a function $f:\Omega\to\mathbb R$, the supremum norm of $x\mapsto cf(x)$ equals $|c|$ times the supremum norm of $f$.

**Proof.** At each $x\in\Omega$, $|cf(x)|=|c|\,|f(x)|$. Since $|c|\ge 0$, taking the supremum over the finite nonempty domain factors out this common nonnegative multiplier. The resulting supremum is $|c|$ times the supremum of $|f|$.
