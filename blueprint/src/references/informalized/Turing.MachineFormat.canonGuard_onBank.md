<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonGuard_onBank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Guard Computation on One Tape

**Claim.** With the stated initial configuration, the guard machine embedded on tape $i$ reaches its done state exactly when the required block fits in the remaining input, and otherwise reaches escape, within the stated time bound; it preserves output, input position as specified, avoids both terminal states earlier, and leaves the other tapes unchanged.

**Proof.** First apply the bounded-run result for the binary guard machine (`Turing.MachineFormat.canonGuard_run`) to the input and parsed pair. It supplies a time at which the guard machine reaches done or escape according to whether the required block fits, along with the output, input-position, and earlier-avoidance conclusions. The parsed header length bound (`Turing.MachineFormat.canonHeader_length`) ensures that the scan's starting position is within the input, and the guard-run time bound is converted to the requested bound using this length estimate and the positivity of the block size. The initial configuration of the embedded machine is identified with the supplied configuration: the one simulated tape is tape $i$, with the specified counter and head position, while the other tapes, input position, state, and output match. This identification follows from the counter-configuration description (`Turing.counter_cfg_eq`) and the embedding equality (`Turing.MachineFormat.canonEmbedEq`). The run-transport theorem for embedded machines (`Turing.embedEmitTM_runFrom`) then transfers the guard run to the embedded machine at every time. Its frame property (`Turing.embedEmitTM_frame`) keeps each tape outside the selected bank, and its head position, fixed; together these give the stated preservation of all other tapes and their head positions.

**Key facts.** `Turing.MachineFormat.canonGuard_run`, `Turing.MachineFormat.canonHeader_length`, `Turing.counter_cfg_eq`, `Turing.MachineFormat.canonEmbedEq`, `Turing.embedEmitTM_runFrom`, `Turing.embedEmitTM_frame`.
