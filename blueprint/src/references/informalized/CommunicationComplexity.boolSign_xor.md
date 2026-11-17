<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean :: CommunicationComplexity.boolSign_xor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign of XOR

**Claim.** For Boolean values $a$ and $b$, the sign of their exclusive-or is the product of their signs.

**Proof.** Check the four possible pairs. When both inputs are false or both are true, their XOR is false and the product of their signs is $1$. When exactly one input is true, their XOR is true and the product is $-1$. Thus the sign of the XOR equals the product in every case.
