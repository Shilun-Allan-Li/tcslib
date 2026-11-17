<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_decider_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cleaning a Binary Decider

**Claim.** If a finite binary Turing machine $M$ decides $L$ within time $T$, then a finite binary Turing machine $R$ decides $L$ within time $n\mapsto B(T(n)+n+2)$ for some natural number $B$.

**Proof.** Apply the installation theorem to the function that maps each input to the one-symbol word recording its membership in $L$. It supplies a machine $C$, designated entry and exit states, and a constant $A$, so that on input $x$ with argument $x$, $C$ reaches the exit state with that one-symbol output after some positive time $t\le A(T(|x|)+|x|+1+1)$; the intermediate-run condition required by the wrapper theorem is also supplied. The single-output wrapper theorem converts this computation into a computation by the cleaned machine $a3RunTM(C)$, preserving the output and giving a time bound $2|x|+2+t+1$ (`a3_run_singleton`). Since $|x|+1\le T(|x|)+|x|+2$, this wrapper bound is at most $(A+3)(T(|x|)+|x|+2)$. Computation persists when the allotted time is increased (`ComputesInTime.mono`). Taking $B=A+3$ proves the assertion for every input.

**Key facts.** `Turing.FinTM.exists_installCallTM`, `Complexity.a3_run_singleton`, `Turing.FinTM.ComputesInTime.mono`.
