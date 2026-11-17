<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.goes_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register-copying loop

**Claim.** If the scratch register is initially zero, the copy loop transfers the source register's value to the destination by adding that value to the destination, restores the source, leaves all other registers unchanged, and preserves the input position and output. It reaches its exit within $7a+2$ steps, where $a$ is the initial source value.

**Proof.** Let $v=\rho(s.src)$ and $d=\rho(s.dst)$. The proof runs the loop in two phases. First, it repeatedly decrements the source; after $j$ iterations the source has value $v-j$, the destination has value $d+j$, and the scratch register has value $j$. Each iteration also increments the destination and scratch once. The source and destination are distinct, neither is the scratch register, and the scratch register starts at zero (`CpS.regs_ne` and the hypothesis). Thus the register updates in this phase do not interfere, and the invariant starts at $\rho$. The loop theorem applies to this phase: the loop tests the source, decrements it, and performs the two increments before returning to the test. Its $v$ iterations take at most $v(2+2)+1=4v+1$ steps (`goes_loop`, `goes_inc`). At the end, the source is zero, the destination is $d+v$, and the scratch register is $v$.

The second phase transfers the scratch value back into the source. After $j$ iterations, the source is $j$ and the scratch register is $v-j$, while the destination remains $d+v$. Each iteration decrements the scratch and increments the source. The loop theorem bounds this phase by $v(1+2)+1=3v+1$ steps (`goes_loop`, `goes_inc`). At completion, the scratch is zero and the source is restored to $v$; together with the first phase's updates, the final register assignment is precisely the original assignment with only the destination changed to $d+v$. The phases compose, preserving the input position and output (`Goes.trans`). Their total cost is $7v+2$, and the final presentation of the register assignment follows by identifying the successive updates (`Goes.congr`).

**Key facts.** `Complexity.UTab.CpS.regs_ne`, `Complexity.CounterProg.goes_loop`, `Complexity.CounterProg.goes_inc`, `Complexity.CounterProg.Goes.mono`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.congr`.
