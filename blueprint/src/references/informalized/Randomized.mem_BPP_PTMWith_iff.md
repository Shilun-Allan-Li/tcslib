<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.mem_BPP_PTMWith_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Randomized Polynomial Time

**Claim.** For any function $p:\mathbb N\to\mathbb Q$ and language $L$ of bit strings, membership in the stated randomized polynomial-time class is equivalent to the existence of the stated polynomial-time Boolean verifier with the required acceptance and rejection probability bounds.

**Proof.** One direction is the construction taking a machine witnessing membership in the randomized polynomial-time class and producing a verifier with the required probability guarantees (`Randomized.inBPPWith_of_mem_BPP_PTMWith`). The converse takes such a verifier and constructs a finite nondeterministic machine witnessing membership in that class (`Randomized.mem_BPP_PTMWith_of_inBPPWith`). Together these two implications give the equivalence.

**Key facts.** `Randomized.inBPPWith_of_mem_BPP_PTMWith`, `Randomized.mem_BPP_PTMWith_of_inBPPWith`.
