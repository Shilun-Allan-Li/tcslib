<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.label_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Party Labels

**Claim.** The map assigning to each nonzero field element its label is injective.

**Proof.** A party is a subtype of the field consisting of nonzero elements, and its label is its underlying field element. If two parties have the same label, their underlying elements are equal, so the parties themselves are equal by injectivity of the subtype's value map.
