<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.agreeOutside_startMem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory preserved outside startup locations

**Claim.** The startup program changes memory only at the constant and pool addresses, the frame-pointer address, and the main-frame stack addresses.

**Proof.** The startup program has the same effect as first performing the constant and pool initialization, then executing the frame program (\texttt{Light.Compiler.startMem_eq}). The first stage preserves agreement outside the constants and pool (\texttt{Light.Compiler.agreeOutside_poolMem}); the second preserves agreement outside the frame-pointer address and main frame (\texttt{Light.Compiler.agreeOutside_frameCode}). Combining the stages yields agreement outside the union of those two sets (\texttt{WordRAM.AgreeOutside.trans_union}).

**Key facts.** `Light.Compiler.startMem_eq`, `Light.Compiler.agreeOutside_poolMem`, `Light.Compiler.agreeOutside_frameCode`, `WordRAM.AgreeOutside.trans_union`.
