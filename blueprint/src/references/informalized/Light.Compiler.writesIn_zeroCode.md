<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.writesIn_zeroCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writes of the Zeroing Code

**Claim.** For every natural number $F$, each instruction in the zeroing code for $F$ writes only to an address in the main frame of size $F$.

**Proof.** Every instruction in the zeroing code is obtained from some $x$ in `List.range F`; hence $x<F$. Its destination is the stack address with index `mainFrame + x`. This index is at least `mainFrame` and strictly less than `mainFrame + F`, so it lies in the index interval defining `MainFrame F`. The instruction is a subtraction, which writes to its destination, and that destination is therefore in the main frame.
