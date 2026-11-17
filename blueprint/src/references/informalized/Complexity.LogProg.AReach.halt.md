<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AReach.halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Guarded Reachability and Halting

**Claim.** If the run from $a$ reaches $b$ with $G$ holding before reaching it, and the run from $b$ halts with answer $r$ while satisfying $G$ before halting, then the run from $a$ halts with answer $r$ and satisfies $G$ before halting.

**Proof.** Let $T_1$ be a time at which the run from $a$ reaches $b$, and let $T_2$ be a halting time for the run from $b$. The run composition law (`Complexity.LogProg.arun_add`) shows that the run from $a$ halts with answer $r$ at time $T_1+T_2$. To verify the guard, consider any $t<T_1+T_2$. If $t<T_1$, the reachability hypothesis gives $G$ at time $t$. Otherwise write $t=T_1+t'$; then $t'<T_2$, and the composition law identifies the configuration at time $t$ with the configuration reached after $t'$ steps from $b$. The halting hypothesis gives $G$ there.

**Key facts.** `Complexity.LogProg.arun_add`.
