<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computation under transverse coding

**Claim.** If the original machine halts on the symbolwise image of a binary input with the symbolwise image of a binary output after $t$ steps, then its transverse binary realization halts on the input with that output after the same number of steps.

**Proof.** The computation characterization of time-bounded acceptance says that the hypothesis supplies two facts: the original machine’s state after $t$ steps is halting, and its output is the encoded word (by `Turing.FinTM.computesInTime_iff`). Apply the exact configuration correspondence after $t$ steps (`Complexity.parallelTM_run`). Its state agrees with the original state, so the encoded machine halts. Its output is the original output mapped through the bit decoder. Substituting the given output makes this the symbolwise image of $w$ mapped through that decoder; the decoder sends each embedded Boolean back to itself (`Complexity.parallelBit_embed`), so the result is $w$. The same computation characterization then yields the claimed time-bounded computation.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Complexity.parallelTM_run`, `Complexity.parallelBit_embed`.
