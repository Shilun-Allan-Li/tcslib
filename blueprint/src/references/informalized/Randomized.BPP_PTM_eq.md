<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.BPP_PTM_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine and Verifier Definitions of BPP

**Claim.** For the specified polynomial-time verifier model, the machine definition of BPP agrees with the verifier definition: a language belongs to polynomial-time BPP exactly when it satisfies the verifier-based BPP condition.

**Proof.** The proof establishes equality of the two sets by extensionality. For each language, the required equivalence between machine-class membership and verifier-based membership is precisely the characterization theorem `mem_BPP_PTM_iff`.

**Key facts.** `Randomized.mem_BPP_PTM_iff`.
