<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.effects_poolCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pool Initialization

**Claim.** If the constant-one cell initially contains the word representation of $1$, then executing the pool initialization code leaves every pool cell with index $n\le N$ equal to the word representation of $n$.

**Proof.** Induct on $N$. For $N=0$, the code consists only of subtracting the constant-one cell from itself into pool cell $0$, so that cell contains zero. For the successor step, split off the final instruction using the code decomposition (`poolCode_succ`). By induction, pool cell $N$ contains $N$ after the preceding code. The preceding code does not alter the constant-one cell, as expressed by its agreement guarantee (`agreeOutside_poolCode`), so the last addition adds $1$ to the value in pool cell $N$ and writes $N+1$ into pool cell $N+1$ (`effect_add`). This establishes the new endpoint; every smaller index is unchanged by that final update, giving the claim for all $n\le N+1$.

**Key facts.** `Light.Compiler.poolCode_succ`, `WordRAM.effects_append`, `WordRAM.effect_add`, `Light.Compiler.agreeOutside_poolCode`, `WordRAM.AgreeOutside.read`.
