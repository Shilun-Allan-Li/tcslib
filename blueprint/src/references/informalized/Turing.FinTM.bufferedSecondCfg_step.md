<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferedSecondCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step second-phase simulation

**Claim.** From a second-phase configuration with a boundary-correct tag, one step of the buffered composition equals the second-phase embedding of the one-step successor of $M_2$, for a suitable boundary-correct successor tag.

**Proof.** Split according to whether $c$ is halted. If it is halted, both machines stay at their current configurations; retaining $b$ preserves the boundary condition and gives the required equality. Otherwise write the active state as $q$, let $a$ be the action chosen by $M_2$, and let $m$ be its input-head movement. The buffer cell under the virtual input head contains exactly the symbol read by $M_2$ (`bufferTape_inputSymbol`), and the right block supplies the same symbols under the work-tape heads. Thus the buffered composition chooses the same action. The virtual-movement correction accounts for attempted moves beyond the virtual input boundaries: `virtualMove_correct` states both that the corrected movement gives the same updated virtual head position and that the updated tag satisfies the boundary condition. The buffered machine leaves the physical input head fixed (`moveInputPos_zero`), preserves the left block, applies $a$'s work-tape actions in the right block, and advances the buffer head according to the corrected movement. These components, together with the successor state and output, are exactly the second-phase embedding of $a$ applied to $c$ with the new tag.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.FinTM.bufferTape_inputSymbol`, `Turing.FinTM.virtualMove_correct`, `Turing.moveInputPos_zero`, `Turing.FinTM.tapeBlocks_buffer`.
