<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.trans_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Composed Running Time

**Claim.** If the first contract has strictly positive running time on every admissible start, then the sequentially composed contract also has strictly positive running time on every admissible start.

**Proof.** Fix an admissible starting configuration. By the assumed positivity of the first contract, its running time is positive. The composed running time is the sum of this time and the second contract's natural-number running time. Adding a natural number cannot decrease the first summand, so the sum remains strictly positive.
