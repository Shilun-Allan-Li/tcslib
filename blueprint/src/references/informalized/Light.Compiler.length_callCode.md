<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Compiler.length_callCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Compiled Calls

**Claim.** The compiled call has length equal to the total argument-expression size plus $1+2G.F+4$.

**Proof.** The call code concatenates the argument code, a newly constructed frame, and one branch instruction. The argument code length is the sum of the argument sizes (Light.Compiler.length_argsCode), and the new frame has length $2G.F+4$ (Light.Compiler.length_newFrame). The final branch contributes one instruction. Adding these three lengths gives $\mathrm{argsSize}(args)+2G.F+5$, which is exactly the stated call size.

**Key facts.** `Light.Compiler.length_argsCode`, `Light.Compiler.length_newFrame`.
