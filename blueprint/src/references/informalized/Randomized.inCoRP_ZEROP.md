<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.inCoRP_ZEROP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Polynomial Testing in coRP

**Claim.** If the specified verifier model declares the zero-testing verifier efficient, then the language of encodings of nonempty, well-formed integer arithmetic circuits computing the zero polynomial belongs to coRP relative to that model.

**Proof.** Use the zero-testing verifier itself as the verifier for the complement, with random-tape length $2400(|x|+1)^2$. Its efficiency is exactly the assumed hypothesis. The verifier specification gives both required probability statements: on inputs outside the zero-polynomial language it accepts with probability at least $2/3$, and on inputs in the language it rejects for every random tape. These are precisely the one-sided guarantees for RP recognition of the complement, hence coRP recognition of the language.

**Key facts.** `Randomized.zeropVerifier_spec`.
