<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.decorateTM_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection commutes with one step

**Claim.** For every decorated configuration, projecting the result of one decorated-machine step onto the schedule gives the result of one original-machine step from the projected configuration.

**Proof.** Split according to whether the decorated configuration is halted. In the halted case both machines leave their configurations unchanged, so the projection identity follows directly. In the running case, write its state as $(q,d)$. The projected configuration has state $q$, the same input-head position and scanned input symbol, and its original work tapes and head positions are precisely the original portions of the decorated ones. Thus the original transition used by the decorated machine is exactly the transition that the original machine uses from the projection. Compare the resulting configurations component by component: their states agree after projecting away the data component, their input-head positions agree, and on each original tape the write and head movement agree. The decorated transition emits the visit function's output, but projection discards output; the original transition emits none by hypothesis, so the projected output also agrees. These component equalities establish equality of the projected configurations.
