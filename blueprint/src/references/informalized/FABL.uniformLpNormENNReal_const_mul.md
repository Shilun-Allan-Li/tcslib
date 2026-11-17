<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLpNormENNReal_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling the extended-exponent uniform norm

**Claim.** For a finite nonempty set $\Omega$, an extended nonnegative real exponent $q\ne 0$, a real number $c$, and a function $f:\Omega\to\mathbb R$, the extended-exponent uniform norm of $x\mapsto cf(x)$ equals $|c|$ times that of $f$.

**Proof.** Split according to whether $q=\infty$. In that case, the extended norm is the supremum norm, and scaling it gives the result by the supremum-norm scaling law (\(\texttt{FABL.uniformLInfinityNorm\_const\_mul}\)). If $q\ne\infty$, the definition uses the finite-exponent norm at the real value of $q$. Since also $q\ne0$, this real exponent is positive; the finite-exponent scaling law then gives the result (\(\texttt{FABL.uniformLpNorm\_const\_mul}\)).

**Key facts.** `FABL.uniformLInfinityNorm_const_mul`, `FABL.uniformLpNorm_const_mul`.
