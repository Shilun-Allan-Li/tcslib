<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.agreeOutside_frameCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory preserved outside the main frame

**Claim.** If $3\le F$, executing the frame-initialization program changes memory only at the frame-pointer address and the main-frame stack addresses.

**Proof.** Every instruction in the frame program writes either the frame-pointer address or a main-frame cell. The initial frame-pointer instruction writes at $cFP$. Each instruction in the zero-initialization segment writes to a main-frame cell, by the characterization of writes in that segment (\texttt{Light.Compiler.writesIn_zeroCode}). The two final instructions write to cells with indices $\mathrm{mainFrame}+1$ and $\mathrm{mainFrame}+2$; the assumption $3\le F$ places both indices in the main frame. Thus every instruction writes within the union of the frame-pointer address and the main frame. The general preservation principle for a list of instructions whose writes lie in a set then shows that the final memory agrees with the initial memory outside that set (\texttt{WordRAM.agreeOutside_effects}); enlarging the set for the zero-initialization writes uses monotonicity of the write-location condition (\texttt{WordRAM.WritesIn.mono}).

**Key facts.** `Light.Compiler.writesIn_zeroCode`, `WordRAM.WritesIn.mono`, `WordRAM.agreeOutside_effects`.
