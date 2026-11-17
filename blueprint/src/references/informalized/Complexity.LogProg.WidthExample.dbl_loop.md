<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.dbl_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubling Loop Register Update

**Claim.** For any language $P$, input word $x$, and natural number $n$ with $2^n\le B$, whenever $a+k=n$, the search program with oracle determined by $P$ can reach location $\mathrm{enum}$ with registers $(0,2^n,0,0)$ from location $\mathrm{dbl}$ with registers $(k,2^a,0,0)$. Throughout the run before reaching that configuration, the program precondition holds and every register is at most $B$.

**Proof.** First, $n\le B$, since $n<2^n$ and $2^n\le B$. Induct on the first exponent $k$, keeping $a$ subject to $a+k=n$. Guards at the configurations used in the run establish the program precondition and the register bounds.

If $k=0$, the relation gives $a=n$. The instruction at $\mathrm{dbl}$ branches on whether register $0$ is zero; here it is zero, so the program reaches $\mathrm{enum}$ without changing the remaining registers. The target accumulator is $2^n=2^a$.

For $k+1$, the program first takes the nonzero branch at $\mathrm{dbl}$, decrements register $0$, and enters the first decrement loop. That loop transfers twice the value $2^a$ into the accumulator, leaving register $0$ zero; the second decrement loop then transfers this accumulated value into the same accumulator and returns to $\mathrm{dbl}$. More precisely, the two loop results compose to give accumulator $0+2\cdot 2^a=2^{a+1}$, with the counter and scratch register zero. The bound follows from $2^{a+1}\le 2^n\le B$. Apply induction with exponents $k$ and $a+1$, whose sum is $n$; this reaches $\mathrm{enum}$ with accumulator $2^n$.

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.WidthExample.guard_rf`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.WidthExample.rf_0`, `Complexity.LogProg.WidthExample.rf_upd0`, `Complexity.LogProg.WidthExample.d1_loop`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.WidthExample.d2_loop`.
