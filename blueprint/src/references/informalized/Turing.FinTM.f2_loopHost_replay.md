<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replaying a Stored Word

**Claim.** Starting with the replay tape containing $w$, its head at zero, active control in phase $13$, and output $o$, the host takes $|w|+1$ steps to a phase-$13$ configuration whose tape still contains $w$, whose head is at $|w|$, and whose output is $ow$, preserving the other data.

**Proof.** The host’s phase-$13$ transition is exactly the replay machine’s transition on the payload tape, with the other tapes left unchanged. This follows by splitting on the symbol currently read from that tape and identifying the host action with the replay action (`f2_loopControl_payload`). The replay-run lemma, applied to the whole word with empty prefix, says that after $|w|+1$ steps the replay machine has halted, moved its head to position $|w|$, retained the word, and appended it to the output (`f2_loopReplay_run`). The right-tape run correspondence then lifts that run to the host, leaving all other specified tapes and heads fixed (`rightCfg_run`).

**Key facts.** `Turing.FinTM.f2_loopControl_payload`, `Turing.FinTM.f2_loopReplay_run`, `Turing.FinTM.rightCfg_run`.
