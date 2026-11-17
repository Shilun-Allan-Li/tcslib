<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.val_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values of the Empty Register Record

**Claim.** The value function of the register record with all fields at their default values assigns $0$ to every register.

**Proof.** Two functions from the 21-register type are equal if they agree at every register. Check each register index in turn; the value function selects the corresponding field of the record, and each field has default value $0$. Hence the value function is constantly zero.
