<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCanon_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Canonizer Completion

**Claim.** After the specified number of steps, the timed canonizer has halted, outputs the serialization of the machine decoded from $\alpha$, has the stated input-head position, and its clock-designated work tape contains $b$ with its head at $|b|$.

**Proof.** Apply the timed run correspondence (`timedCanon_run`) at $t=c.\mathrm{canonizerTime}(|\alpha|)$. It identifies the timed canonizer's configuration with a buffered second-phase configuration built from the canonizer's run on $\alpha$ at that time. The defining computation-time property of the canonizer, converted to its explicit halting-and-output form by `computesInTime_iff`, says that this run has halted and its output is $(c.\mathrm{decode}(\alpha)).\mathrm{serialize}$. Substituting those two facts into the buffered configuration gives the claimed halting state and output; the input position is already the fixed position in the correspondence. The buffered configuration also specifies the clock tape as the buffer holding $b$ and its head at $|b|$, which yields the remaining assertions.

**Key facts.** `Turing.timedCanon_run`, `Turing.FinTM.computesInTime_iff`.
