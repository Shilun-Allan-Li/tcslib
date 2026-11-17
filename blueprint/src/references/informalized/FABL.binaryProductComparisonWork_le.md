<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryProductComparisonWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Comparison Work Bound

**Claim.** For every natural number $\ell$, the product comparison work is at most $4(\ell+1)^2$.

**Proof.** Use the exact formula $(2\ell+1)(2\ell+2)$ for the product comparison work ($\texttt{binaryProductComparisonWork_eq}$). Expanding both sides, the desired inequality reduces to $4\ell^2+6\ell+2\leq4\ell^2+8\ell+4$, which holds since $2\ell+2\geq0$.

**Key facts.** `FABL.binaryProductComparisonWork_eq`.
