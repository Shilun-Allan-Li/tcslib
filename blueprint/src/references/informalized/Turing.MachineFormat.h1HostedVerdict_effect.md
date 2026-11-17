<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.h1HostedVerdict_effect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hosted summary effect

**Claim.** For a machine $M$ and a step-block configuration representing its initial configuration, the hosted verdict machine halts within the stated bound, returns to input-head position $p$, and appends the time-$t$ summary bit to the existing output.

**Proof.** 1. Use the hosted-loop simulation theorem with the machine’s initial configuration, the represented configuration $d$, the binary encoding of $t$ as counter, and the supplied input-head position. The theorem gives a bounded run of the hosted loop, together with the representation facts tracking the simulated configurations through time $t$ and a final hosted configuration at the loop’s exit. The binary counter identity identifies the value represented by the counter tape with $t$.

2. The verdict machine agrees with the hosted loop on states other than its two exit states. The lockstep cut property, applied to the run’s guarantee that those exits are not reached prematurely, therefore transfers the loop run through its final pre-verdict step to the verdict machine.

3. The summary-clock correctness theorem identifies the accumulated summary with the conjunction that the simulated machine is halted at time $t$ and that its output summary is true. The hosted-loop read theorem supplies the represented final configuration and the value on the summary tape. One more transition of the verdict machine reads that cell, emits the corresponding verdict bit, and halts; its input head does not move, so it remains at $p$. The counter/configuration identity and the zero-move identity justify the final configuration bookkeeping. The extra transition increases the time bound by one, giving the stated bound.

**Key facts.** `Turing.StepBlock.hostedLoopTM_run`, `Turing.counterValue_bits`, `Turing.MultiTapeTM.runFrom_eq_of_agreeOn`, `Turing.Lockstep.cut`, `Turing.MachineFormat.summaryClock_correct`, `Turing.StepBlock.hostedLoop_read`, `Turing.counter_cfg_eq`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
