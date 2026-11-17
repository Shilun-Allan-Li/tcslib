<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arSpacePhase_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulator phase after one step

**Claim.** If the simulator configuration is in a phase associated with a source configuration, then after one simulator step it is either still in a phase associated with that source configuration or is in a phase associated with the next source configuration.

**Proof.** First consider the case where the simulator configuration is exactly the encoding of the source configuration. If the source has halted, its step leaves it unchanged (`Turing.MultiTapeTM.step_of_halt`), so the simulator remains in the encoded phase. If the source state is $q$, the simulator starts reading the encoded work-tape blocks; its next configuration is the reading phase at index $1$ (`arReadCfg_zero`, `arReadCfg_step`). Otherwise the given phase is one of reading, writing, or moving, all associated with a nonhalting state $q$. In a reading phase, an index below $N+1$ advances to the next reading index (`arReadCfg_step`). At the final index, dispatch begins the writing phase (`arReadCfg_dispatch`). In a writing phase, a positive index decreases (`arWriteCfg_step`); at index zero, writing finishes and the simulator enters the moving phase (`arWriteCfg_finish`). In a moving phase, a positive remaining movement index decreases while preserving the source association (`arMoveCfg_step`). At index zero, movement finishes: the simulator is the encoding of the source configuration after its transition (`arMoveCfg_finish`), so it is associated with the next source configuration. These cases exhaust the phase alternatives and establish the stated one-step property.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.FinTM.arReadCfg_zero`, `Turing.FinTM.arReadCfg_step`, `Turing.FinTM.arReadCfg_dispatch`, `Turing.FinTM.arWriteCfg_step`, `Turing.FinTM.arWriteCfg_finish`, `Turing.FinTM.arMoveCfg_step`, `Turing.FinTM.arMoveCfg_finish`.
