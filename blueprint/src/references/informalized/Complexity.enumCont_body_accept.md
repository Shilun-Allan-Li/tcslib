<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance emits true

**Claim.** From the specified body-machine configuration in administrative state $3$, one step halts and appends exactly the bit true to the output.

**Proof.** The proof unfolds the body-machine transition and the given configuration. At administrative state $3$, the transition emits true and enters the halting state; it makes no work-tape changes. Applying this action therefore leaves the tape contents and head positions as specified and appends the one-letter word $[\mathrm{true}]$ to the initially empty output. The transition's state and output fields give the two asserted equalities.
