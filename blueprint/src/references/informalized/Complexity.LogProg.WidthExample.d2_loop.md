<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.d2_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Decrement Loop Register Update

**Claim.** For any language $P$, input word $x$, and bound $B$, suppose $i,u\le B$. For every $b,p\in\mathbb N$ with $p+b\le B$, the search program, using its oracle determined by $P$, can reach the configuration at location $\mathrm{dbl}$ with registers $(i,p+b,0,u)$ from location $\mathrm{d2}$ with registers $(i,p,b,u)$, without leaving the configurations satisfying the program precondition and the bound $B$ on every register at any earlier step.

**Proof.** Induct on the counter $b$, keeping $p$ arbitrary. Each step of the constructed run is preceded by the register guard (`guard_rf`), which ensures both the program precondition and the bound on all registers.

When $b=0$, the instruction at $\mathrm{d2}$ branches directly to $\mathrm{dbl}$, since the counter is zero, and the registers already have the desired values. For $b+1$, the program takes the nonzero branch, decrements the counter, and increments the accumulator $p$. It returns to $\mathrm{d2}$ with registers $(i,p+1,b,u)$. The hypothesis $p+(b+1)\le B$ bounds these intermediate values, and induction with accumulator $p+1$ reaches $\mathrm{dbl}$ with accumulator $(p+1)+b=p+(b+1)$ and counter zero.

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.WidthExample.guard_rf`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.WidthExample.rf_2`, `Complexity.LogProg.WidthExample.rf_upd2`, `Complexity.LogProg.WidthExample.rf_1`, `Complexity.LogProg.WidthExample.rf_upd1`.
