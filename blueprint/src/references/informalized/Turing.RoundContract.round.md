<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.RoundContract.round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A round satisfies its contract

**Claim.** For any configuration in the anchor state satisfying the round precondition, the run for the contract duration has the prescribed endpoint, positive duration, no forbidden intermediate state, and head positions within the contract bounds throughout.

**Proof.** Unpack the round contract’s defining guarantees at the given parameter and configuration. The starting-state hypothesis gives the required anchor state; the contract supplies the positive duration and identifies the run at that duration with the prescribed endpoint, whose state lies in the anchor-or-escape set. Its cut condition excludes halted, anchor, and escape states at every positive intermediate time, while its envelope condition places each work-head position in the stated coordinate interval at every time up to and including the endpoint. Together these are precisely the clauses of a round.
