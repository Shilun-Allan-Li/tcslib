<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_clear_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Cleanup of a Visited Tape

**Claim.** The cleaner reaches state $3$ with all three tapes blank and all heads at the origin within $6T+7$ steps, and does not reach state $3$ earlier.

**Proof.** First, `emCall_track_clearable` gives a time $t\le 6T+7$ at which the cleaner, started in state $0$ with the specified data, interval marker, origin marker, and head position, reaches the configuration in state $3$ with all three tapes blank and all heads at the origin. State $3$ is fixed by the cleaner: its transition is a zero-move control action that leaves the configuration unchanged. The fixed-state criterion in `emCall_first_entry` then finds the first time $a\le t$ at which this terminal configuration occurs and guarantees that no earlier time is in state $3$. It also preserves the same terminal configuration at time $a$. The time is positive, since a configuration starting in state $0$ cannot already have the state-$3$ endpoint at time zero. Hence $0<a\le 6T+7$, with the asserted first-entry property.

**Key facts.** `Turing.FinTM.emCall_track_clearable`, `Turing.FinTM.emCall_first_entry`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
