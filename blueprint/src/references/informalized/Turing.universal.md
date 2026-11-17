<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.universal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Universal Simulation

**Claim.** For every effective coding scheme, there is a finite-tape Boolean machine that simulates each decoded machine with a code-dependent linear time bound and whose halting outputs correspond exactly to those of the decoded machine.

**Proof.** Choose the universal machine and the startup and per-step bounds specified by the construction. The universal-start lemma (Turing.universalRelation_start) places its initial run in the simulation relation after a bounded startup. The block simulation theorem (Turing.universal_from_blocks) then converts this startup bound, the per-step bound, and the relation’s halting and output properties into the claimed time and correctness statements. To verify its per-step hypothesis, split on whether the simulated configuration is already halted. If it is halted, the machine stays at that configuration by the halt-step facts (Turing.MultiTapeTM.step_of_halt and Turing.MultiTapeTM.runFrom_of_halt); the relation’s halting equivalence and output agreement are supplied by (Turing.universalRelation_halt) and (Turing.universalRelation_output). If it is live, the live-block lemma (Turing.universal_live_block) gives a bounded interpreter run to the next simulated configuration. The capture simulation identity (Turing.universalCapture_interpreter_run) lifts that run to the full universal machine while preserving its auxiliary tapes. Thus each simulated step takes at least one and at most the stated code-dependent number of universal steps, and the block simulation theorem gives both the exact linear time bound when the decoded machine halts after $t$ steps and the converse correspondence of halting outputs.

**Key facts.** `Turing.universalRelation_start`, `Turing.universal_from_blocks`, `Turing.MultiTapeTM.step_of_halt`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.universalRelation_halt`, `Turing.universalRelation_output`, `Turing.universal_live_block`, `Turing.universalCapture_interpreter_run`.
