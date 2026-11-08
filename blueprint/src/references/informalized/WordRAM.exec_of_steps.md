<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.exec_of_steps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution from a sequence of steps

**Claim.** If $c$ reaches $c'$ through $n$ continuing steps and the next step from $c'$ halts with verdict $v$, then execution from $c$ for $n+1$ steps returns $v$ and the memory of $c'$.

**Proof.** Induct on the number $n$ of continuing steps, allowing the starting configuration to vary. When $n=0$, the definition of the step sequence says $c=c'$. The halting-step equation then gives execution for one step as verdict $v$ with the memory of $c'$. For $n+1$, the step sequence provides an intermediate configuration $c_1$: the first step continues from $c$ to $c_1$, and $c_1$ reaches $c'$ in $n$ steps. The continuing-step equation reduces execution from $c$ for $n+2$ steps to execution from $c_1$ for $n+1$ steps (`WordRAM.exec_succ_of_step`). Applying the induction hypothesis to the remaining sequence, with the same halting step from $c'$, yields verdict $v$ and memory $c'.mem$.

**Key facts.** `WordRAM.exec_succ_of_verdict`, `WordRAM.exec_succ_of_step`.
