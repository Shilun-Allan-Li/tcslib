<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.seq_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential Composition Has Positive Duration

**Claim.** Under the stated linkage of admissible starts to the second contract’s precondition, the sequentially composed contract has strictly positive duration for every admissible start in its entry state.

**Proof.** For any admissible start, the composed duration is the sum of the first contract’s duration, one transition step at the seam, and the second contract’s duration. The seam contributes one, so the total is at least one and is therefore strictly positive.
