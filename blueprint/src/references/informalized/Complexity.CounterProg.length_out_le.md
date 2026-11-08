<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean :: Complexity.CounterProg.length_out_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Output Length

**Claim.** If $t\le C(n+1)^c$, then the output after $t$ steps from the initial state has length at most $(C+1)^2(n+1)^{2c}$.

**Proof.** The output-length estimate for a run from the initial state gives length at most $t(t+1)$ (\texttt{run\_init\_out\_le}). Put $N=(n+1)^c$. Since $n+1\ge 1$, we have $1\le N$, and the time hypothesis gives $t\le CN$. Consequently $t+1\le (C+1)N$, so $t(t+1)\le (CN)((C+1)N)\le ((C+1)N)^2$. Finally, $N^2=(n+1)^{2c}$, yielding the claimed bound.

**Key facts.** `Complexity.CounterProg.run_init_out_le`.
