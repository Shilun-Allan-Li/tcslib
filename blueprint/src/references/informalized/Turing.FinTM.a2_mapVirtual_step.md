<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_mapVirtual_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step virtual simulation

**Claim.** A correctly tagged virtual configuration has a one-step successor corresponding to the simulated machine's successor, with the virtual input position, first buffer, and output prefix retained.

**Proof.** Split first on whether the simulated machine is halted. If it is, its step leaves the configuration unchanged (`Turing.MultiTapeTM.step_of_halt`); choosing the same tag gives the required boundary condition and the virtual configuration is unchanged as well.

Otherwise let the simulated transition action be the action prescribed by $M$ at the current state, input symbol, and work-tape symbols. The middle buffer in the virtual configuration presents exactly the simulated input symbol (`Turing.FinTM.bufferTape_inputSymbol`), while the right-hand tapes present the simulated work-tape symbols. The one-step rule for the mapped machine therefore uses this same simulated action. Its input-head movement is adjusted by `virtualMove`; the correctness lemma for that adjustment (`Turing.FinTM.virtualMove_correct`) gives both the updated encoded input-head position and a tag correctly marking the new boundary. Choose the new tag specified there.

It remains to identify the resulting configurations. The first buffer's head and contents are unchanged, and the simulated work tapes receive precisely the simulated action's writes and movements. The middle buffer head moves by the adjusted movement, which the same correctness lemma identifies with the new encoded simulated input-head position. Zero movement fixes the outer input-head position (`Turing.moveInputPos_zero`). Finally, the output lists agree because appending the simulated output symbol after the existing prefix is associative. These componentwise identities establish the claimed equality.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.FinTM.bufferTape_inputSymbol`, `Turing.FinTM.virtualMove_correct`, `Turing.moveInputPos_zero`, `Turing.FinTM.tapeBlocks_buffer`.
