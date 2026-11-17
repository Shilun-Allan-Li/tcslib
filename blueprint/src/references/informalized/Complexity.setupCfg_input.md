<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol in a Setup Configuration

**Claim.** The input symbol read in a setup configuration is blank when the head position is zero; otherwise it is the schedule word's symbol at index $p-1$, if that index exists, and blank if it does not.

**Proof.** A setup configuration retains the input-head position $p$ of its base configuration, so its read symbol is determined solely by that position and the input word. By the definition of the input-symbol operation, position zero gives blank; at any other position it reads the input at index $p-1$, with an out-of-range list lookup interpreted as blank. Expanding the setup configuration and simplifying its head-position field gives exactly the stated option-valued lookup.
