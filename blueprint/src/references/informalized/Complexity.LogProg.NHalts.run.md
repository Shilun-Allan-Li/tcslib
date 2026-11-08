<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Along a Deterministic Run

**Claim.** If the fixed deterministic run takes $a$ to $a'$ in $T$ steps, satisfies $G$ at every earlier time, and has deterministic instructions whenever live before time $T$, then halting within $N$ steps from $a'$ implies halting within $T+N$ steps from $a$.

**Proof.** Fix a choice word $\sigma$ of length $T+N$. Its first $T$ bits have length $T$ and, because every live instruction before time $T$ is deterministic, the nondeterministic run on that prefix agrees with the deterministic run; hence it reaches $a'$ (`narun_eq_arun` and the assumed equality of the deterministic run). The remaining suffix has length $N$, so the assumed halting property from $a'$ applies. Decomposing the word into prefix and suffix identifies the full run with that suffix run from $a'$ (`narun_append`), proving the endpoint is halted. Now take any $t<T+N$. If $t<T$, the run on its prefix agrees with the deterministic run through time $t$, and therefore satisfies $G$ by hypothesis. If $t\ge T$, split its prefix at $T` (`take_split`). The run is then the run from $a'$ on the next $t-T$ bits, and the guard condition follows from the assumed halting property there, since $t-T<N$. In either case the conclusion applies whenever the configuration is live.

**Key facts.** `Complexity.LogProg.narun_eq_arun`, `Complexity.LogProg.narun_append`, `Complexity.LogProg.take_split`.
