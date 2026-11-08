<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.guardBlock_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One interior guard step

**Claim.** From position $j$ in phase $u$, if $u<b+1$ and $j<|x|$, one guard-machine step reaches position $j+1$ in phase $u+1$, leaving the output unchanged.

**Proof.** Since $j<|x|$, the cell at position $j$ contains the corresponding input symbol rather than a blank. The input-symbol identification lemma (Turing.inputSymbolInner) makes the transition take its scanning branch. As $u<b+1$, the phase counter's residue is $u$, so that branch advances it to phase $u+1$. The input-only action rule (Turing.step_of_inputMoveAction) gives the successor state and a positive head movement; the head-position formula (Turing.moveInputPos_pos_of_ne_right) shows this moves from $j$ to $j+1$. The action does not write to work tapes or append output, and equality of configurations with zero work tapes is determined by state, input position, and output (Turing.Cfg.ext_zero_tapes).

**Key facts.** `Turing.inputSymbolInner`, `Turing.step_of_inputMoveAction`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
