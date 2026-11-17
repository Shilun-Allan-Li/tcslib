<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.boolOfSign_signOfBool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean and sign conversion

**Claim.** For every Boolean value $b$, converting $b$ to its associated sign and then back to a Boolean recovers $b$.

**Proof.** There are two cases. If $b$ is false, its associated sign is $1$, which is not $-1$, so the sign-to-Boolean rule returns false. If $b$ is true, its associated sign is $-1$, so that rule returns true. In either case the original Boolean is recovered.
