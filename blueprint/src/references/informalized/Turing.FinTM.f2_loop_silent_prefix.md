<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_silent_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Output on Every Earlier Step

**Claim.** If the output after $t$ steps is empty, then it is empty after every $u\le t$ steps.

**Proof.** Output at an earlier time is a prefix of output at a later time: apply the output-prefix theorem to $u\le t$ (`Turing.MultiTapeTM.output_prefix`). Since the later output is empty, its only prefix is the empty list, so the output at time $u$ is empty as well.

**Key facts.** `Turing.MultiTapeTM.output_prefix`.
