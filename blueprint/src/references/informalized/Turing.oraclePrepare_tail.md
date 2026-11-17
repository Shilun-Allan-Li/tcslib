<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oraclePrepare_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Oracle Preparation Tail

**Claim.** From the origin-walk configuration at position zero, the dispatch machine reaches the ready configuration with empty argument and copy state after exactly two steps.

**Proof.** At the origin state with the first two heads at cell $0$, the true origin marker is present under the second head. The first transition therefore takes the branch that records the saved tape symbol and moves into the save phase. Since $p\ne0$, the saved location is distinct from the origin cell; the second transition completes the restoration and marker setup, resets the heads as specified, and enters the copy state with an empty argument. The resulting tape contents, head positions, input position, and output agree with the ready configuration.
