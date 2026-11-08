<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.recombine_eq_eval_interpolate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recombination by interpolation

**Claim.** For a finite set of nonzero field elements, recombining the values of a function equals the value at zero of the polynomial interpolating those values on the set.

**Proof.** The interpolation polynomial is the finite sum of Lagrange basis polynomials, each multiplied by the function's value at its corresponding party. Evaluating this sum at zero gives the sum of the basis values at zero times those function values. By definition, those basis values at zero are the recombination coefficients, so the resulting sum is exactly recombination.
