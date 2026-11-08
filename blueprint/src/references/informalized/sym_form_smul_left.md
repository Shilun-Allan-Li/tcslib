<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: sym_form_smul_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity in the first argument

**Claim.** The standard symplectic form is homogeneous in its first argument: $\langle cx,y\rangle=c\langle x,y\rangle$.

**Proof.** Expand the definition into its two coordinate sums. In each sum, the scalar $c$ multiplying the relevant coordinate of $x$ can be factored out of the finite sum. The resulting difference is $c$ times the difference of the original sums, using distributivity of multiplication over subtraction. This is the desired identity.
