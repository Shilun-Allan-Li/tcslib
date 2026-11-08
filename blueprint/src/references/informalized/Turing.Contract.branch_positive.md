<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.branch_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of a branched contract

**Claim.** Under the stated endpoint-precondition assumptions, the branched contract has strictly positive duration on every admissible starting configuration.

**Proof.** Fix any datum and starting configuration satisfying the branched contract's entry and precondition hypotheses. Its duration is one transition for the branch change plus a natural-number duration for the selected branch. A natural-number duration is nonnegative, so the total is at least one and hence strictly positive.
