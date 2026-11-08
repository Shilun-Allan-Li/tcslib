<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundTM_firstExit_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unique First Exit Time

**Claim.** There is exactly one positive time when the round machine is in either its entry state or its halt state, and at every strictly intermediate positive time it is in neither state.

**Proof.** The round-machine effect theorem (`Turing.StepBlock.roundTM_effect`) supplies a positive time $T$ whose endpoint state is the exit state—entry when the successor remains live, halt otherwise—and guarantees that all strictly intermediate positive times avoid both states. This proves existence. For uniqueness, suppose another positive time $T'$ has the same endpoint property and avoids both exit states at every intermediate positive time. If $T'<T$, the first run's intermediate-state guarantee says the machine is in neither exit state at $T'$, contradicting the assumed exit property there. If $T'>T$, the second run's intermediate-state guarantee applied at $T$ says the machine is in neither exit state at $T$, contradicting the first run's exit property. Thus neither strict inequality is possible, so $T'=T$.

**Key facts.** `Turing.StepBlock.roundTM_effect`.
