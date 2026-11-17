<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_false_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejecting at a False Input Bit

**Claim.** If $j<|x|$ and $x_j$ is false, then from the scan configuration at position $j$ with buffer $u$, either choice bit causes the machine to halt and output `[false]` in one step.

**Proof.** The scan-state transition rule `uw_step_scan` identifies this step with the machine's transition from state $0$. At position $j$, the input head reads $x_j$ by `inputSymbolInner`; since this bit is false, the transition rule sends the machine directly to its halting state and appends the false output bit. The resulting state is halted and the output is `[false]`, independently of the choice bit.

**Key facts.** `Complexity.uw_step_scan`, `Turing.inputSymbolInner`.
