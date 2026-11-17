<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryModulusSearchWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Modulus Search Work Bound

**Claim.** For every natural number $\ell$, the binary modulus search work is at most $9(\ell+1)^2 2^{3\ell}$.

**Proof.** Use the modulus search work formula ($\texttt{binaryModulusSearchWork_eq}$) to write the work as $2^\ell$ times the factor search work plus one. The factor search bound ($\texttt{binaryFactorSearchWork_le}$) bounds that work by $8(\ell+1)^2 2^{2\ell}$. Since $(\ell+1)^2 2^{2\ell}\geq 1$, adding one raises this bound to at most $9(\ell+1)^2 2^{2\ell}$. Multiplying by $2^\ell$ preserves the inequality. Finally, $2^\ell 2^{2\ell}=2^{3\ell}$, giving the stated bound.

**Key facts.** `FABL.binaryModulusSearchWork_eq`, `FABL.binaryFactorSearchWork_le`.
