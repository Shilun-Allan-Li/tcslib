<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.recombine_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of recombination

**Claim.** Recombining the shares obtained by multiplying every value of a function by a field element $c$ gives $c$ times the recombination of the original function.

**Proof.** Expand recombination as a finite sum of its coefficients multiplied by the corresponding shares. In each summand, the share is $c f(i)$, so associativity and commutativity of field multiplication move $c$ outside that summand. Distributing multiplication by $c$ over the finite sum gives $c$ times the original recombination.
