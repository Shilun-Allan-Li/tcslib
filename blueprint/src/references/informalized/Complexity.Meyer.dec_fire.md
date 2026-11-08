<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.dec_fire -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Simulated Step During a Sweep

**Claim.** When the counter buffer has true at its current head position, the simulator's decode state performs the corresponding step of $M$, updates that counter cell to false, and moves its counter head one position left, while retaining the output buffer and its head.

**Proof.** Let $a$ be the transition chosen by $M$ from state $q$ using the symbols read from $c$, and let $m$ be its input-head movement after applying the virtual boundary correction. The virtual-movement correctness lemma ensures both that the simulated input-head coordinate moves to the coordinate prescribed by $M$ and that the updated boundary tag $b'=\mathrm{virtualNextTag}(b,m)$ correctly marks the new position (`virtualMove_correct`). Since the counter buffer reads true at $z_C$, the simulator's decode transition takes its firing branch: it uses $a$ on the simulated work tapes, writes false to the counter cell, and moves the counter head by $-1$. The one-step simulator description identifies this transition with applying the selected action to the lifted configuration (`lcfg_step`); the auxiliary-buffer read lemmas identify the input and counter symbols supplied to the transition (`aux_read0`, `aux_read1`), and the simulated work-tape reads reduce to those of $c$ (`mreads`). The action-application formula (`tact_apply`) then gives the updated configuration. Its output register is updated by appending $a$'s optional output, which agrees with the output register of the successor configuration by `OutReg.ofList_push`. Finally, the virtual-movement identity gives the new simulated input position, while the other auxiliary head movements are respectively $-1$ and $0$. Comparing the tape contents and head positions yields exactly the stated lifted successor configuration.

**Key facts.** `Turing.FinTM.virtualMove_correct`, `Complexity.Meyer.lcfg_step`, `Complexity.Meyer.aux_read1`, `Complexity.Meyer.aux_read0`, `Complexity.Meyer.mreads`, `Complexity.Meyer.tact_apply`, `Complexity.TimeHierarchy.OutReg.ofList_push`.
