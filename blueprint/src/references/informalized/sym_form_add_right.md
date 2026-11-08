<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_add_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity in the second argument

**Claim.** The standard symplectic form is additive in its second argument: $\langle x,y+z\rangle=\langle x,y\rangle+\langle x,z\rangle$.

**Proof.** Expand the second argument coordinatewise. For each coordinate $i$, distributivity rewrites $x_X(i)(y_Z(i)+z_Z(i))-x_Z(i)(y_X(i)+z_X(i))$ as the sum of the expressions involving $y$ and $z$ separately. Summing over all coordinates distributes the finite sum over addition, yielding the claimed equality.
