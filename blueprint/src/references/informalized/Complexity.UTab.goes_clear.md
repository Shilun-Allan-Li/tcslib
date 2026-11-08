<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.goes_clear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing a Counter Register

**Claim.** For any clearing mode, the program reaches that mode’s exit after at most $2\rho(r)+1$ steps, where $r$ is its selected register. Only that register changes, becoming zero; the input position and output remain unchanged.

**Proof.** Let $r$ be the register selected by the clearing mode, and after $j$ decrements let the register state be $\rho_j$, obtained from $\rho$ by replacing its value at $r$ with $\rho(r)-j$. The routine first tests $r$: if it is zero it exits, and otherwise it decrements $r$ and returns to the test. For each iteration before the value reaches zero, the body consists of a zero-step stay at the loop body, with no output and no input movement; its register update agrees with passing from $\rho_j$ to $\rho_{j+1}$ when the loop’s decrement is accounted for.

The loop principle (`goes_loop`) therefore applies with $K=\rho(r)$: the counter decreases from $K$ to zero, each iteration emits the empty word, and the program exits when the test finds zero. The initial tracked state is exactly $\rho$, and the final tracked state is $\rho$ with register $r$ replaced by zero. The loop uses $K(0+2)+1=2\rho(r)+1$ steps. Register-state and output equalities are then identified with the claimed forms, using the fact that a program state relates to itself with no output or input change (`goes_refl`) and adjusting the resulting equalities and bound (`Complexity.CounterProg.Goes.congr`).

**Key facts.** `Complexity.CounterProg.goes_loop`, `Complexity.UTab.goes_refl`, `Complexity.CounterProg.Goes.congr`.
