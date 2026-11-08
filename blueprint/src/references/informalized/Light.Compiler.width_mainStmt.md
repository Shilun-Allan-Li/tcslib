<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.width_mainStmt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Main Statement Width

**Claim.** For every natural number $p_0$, the width of the main statement calling procedure $p_0$ with arguments given by variables $1$ and $2$, and storing the result in variable $0$, is exactly $3$.

**Proof.** The statement is a call with two arguments. Its destination contributes $0+1=1$ to the width, and the argument list has length $2$. Each variable argument has width $2$: its variable bound is $1+1=2$ or $2+1=3$, while its height is $1$, so the two widths are $2$ and $3$. Thus the maximum of the destination bound, argument count, and argument widths is $3$.
