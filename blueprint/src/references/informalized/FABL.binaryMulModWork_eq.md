<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMulModWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work of Binary Modular Multiplication

**Claim.** For every natural number $\ell$, the work assigned to binary modular multiplication is $\ell(6\ell+2)$.

**Proof.** Binary modular multiplication runs the multiplication state for $\ell$ steps. Substituting $r=\ell$ into the state-work formula (`binaryMulModStateWork_eq`) gives $\ell(6\ell+2)$.

**Key facts.** `FABL.binaryMulModStateWork_eq`.
