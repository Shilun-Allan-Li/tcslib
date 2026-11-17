<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.exec_succ_of_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution after a continuing step

**Claim.** If one step from $c$ continues at $c'$, then for every $t\ge0$, execution from $c$ for $t+1$ steps equals execution from $c'$ for $t$ steps.

**Proof.** The one-step execution equation expresses execution for $t+1$ steps as a case distinction on the result of the first step: a halting verdict gives its halted result, while a continuing step at a next configuration gives execution for $t$ steps from that configuration (`WordRAM.exec_succ`). Under the hypothesis that the first step from $c$ continues at $c'$, this case distinction selects precisely execution from $c'$ for $t$ steps.

**Key facts.** `WordRAM.exec_succ`.
