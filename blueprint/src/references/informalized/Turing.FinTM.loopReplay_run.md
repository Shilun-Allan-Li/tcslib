<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopReplay_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay of a Remaining Suffix

**Claim.** Starting from a live replay configuration with tape contents PR, head at |P|, and output O, replaying the suffix R for |R|+1 steps halts with tape contents PR, head at |PR|, and output OR.

**Proof.** Induct on the suffix R, allowing the prefix and current output to vary. If R is empty, the one-step replay rule halts, leaves the tape and output unchanged, and keeps the head at the prefix length; this is the desired result since the suffix adds no symbols. If R begins with a bit b, the first step emits b, advances the head by one, and remains live, while leaving the stored word unchanged. Apply the induction hypothesis to the remaining suffix, with prefix P extended by b and output O extended by b. It gives a halted configuration after the remaining suffix length plus one steps, with the head at the total word length and output O followed by b and then the remaining suffix. Associativity of concatenation identifies this with OR. The one-step behavior used here is the replay transition rule (`loopReplay_step`); the conversion of a run of one more step into one step followed by a shorter run is the run recurrence (`runFrom_succ_eq_step`).

**Key facts.** `Turing.FinTM.loopReplay_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
