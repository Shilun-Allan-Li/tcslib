<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_smul_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity in the second argument

**Claim.** The standard symplectic form is homogeneous in its second argument: $\langle x,cy\rangle=c\langle x,y\rangle$.

**Proof.** Expand the definition into the two coordinate sums. Commutativity and associativity of multiplication put the scalar $c$ in front of each coordinate product, after which it factors out of each finite sum. Distributing multiplication over subtraction then gives $c$ times the original symplectic form.
