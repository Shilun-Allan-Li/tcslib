<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Sharing.lean :: TCSlib.Shamir.recombine_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of reconstruction

**Claim.** Recombining the pointwise sum of a finite family of share functions equals the sum of their individual recombinations.

**Proof.** Expand the left-hand recombination as a sum over parties, with each term containing the sum of shares over the finite family. Distribute multiplication by the party's recombination coefficient across that inner sum. The result is a finite sum over pairs consisting of a party and a family index. Interchanging the order of these finite sums groups terms by family index, yielding the sum of the individual recombinations.
