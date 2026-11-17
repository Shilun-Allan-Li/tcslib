<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.size_mainStmt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Main Statement Size

**Claim.** For every procedure index $p_0$ and frame parameter $F$, the size of the main statement is $2F+11$.

**Proof.** The main statement is a call with two arguments, the variables at indices $1$ and $2$. Each variable expression has size $2$, so the total argument size is $4$. The call-code size is therefore $4+1+2F+4=2F+9$. A call statement adds two more instructions to this size, giving $2F+11$.
