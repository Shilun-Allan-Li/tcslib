<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.InCoRP.inBPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoRP implies BPP under complementation

**Claim.** If efficient verifiers are closed under Boolean negation, then a language whose complement is in RP is in BPP.

**Proof.** The assumption that the complement of $L$ is in RP yields an BPP verifier for that complement, because RP is contained in BPP (Randomized.InRP.inBPP). Closure of efficient verifiers under Boolean negation then gives a BPP verifier for the complement of that language (Randomized.InBPP.compl). Since the complement of the complement of $L$ is $L$, this proves the claim.

**Key facts.** `Randomized.InRP.inBPP`, `Randomized.InBPP.compl`.
