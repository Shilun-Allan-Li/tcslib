<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostEmitTM_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Virtual Simulation

**Claim.** One step of the virtual simulation agrees with the encoded one-step successor of $M$, for a suitable updated Boolean tag that satisfies the boundary condition.

**Proof.** If $c$ is halted, both machines stay at their current configurations. Choosing the same tag $b$ preserves the boundary condition, and the encoded configurations agree by their definitions. Otherwise write $c$'s state as $q$, let $a$ be the action prescribed by $M$ from $q$ and the symbols under its heads, and let $mv$ be the virtual input-head movement obtained from $b$, the input symbol, and $a$'s input movement. The virtual buffer tape presents exactly $c$'s input symbol (`Turing.FinTM.bufferTape_inputSymbol`), while each bank presents the corresponding work-tape symbol. Thus the virtual transition uses the same action $a$ on the bank tapes. The virtual-movement correctness lemma (`Turing.FinTM.virtualMove_correct`) says both that the buffer head's new position represents the new input-head position of $M$ and that the updated tag, chosen as the virtual next tag, satisfies the boundary condition. The virtual input head itself stays fixed, and the extra buffer tape is updated to the new represented input position; the bank heads, tapes, state, and output then agree componentwise with the encoding of $a$ applied to $c$.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.FinTM.bufferTape_inputSymbol`, `Turing.FinTM.virtualMove_correct`, `Turing.moveInputPos_zero`.
