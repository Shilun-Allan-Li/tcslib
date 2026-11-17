<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_add_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity in the first argument

**Claim.** The standard symplectic form is additive in its first argument: $\langle x+y,z\rangle=\langle x,z\rangle+\langle y,z\rangle$.

**Proof.** Expand the first argument coordinatewise. For each coordinate $i$, distributivity gives $(x_X(i)+y_X(i))z_Z(i)-(x_Z(i)+y_Z(i))z_X(i)$ as the sum of the corresponding expressions for $x$ and $y$. Summing these coordinatewise equalities over all $i$ and distributing the finite sum over addition proves the identity.
