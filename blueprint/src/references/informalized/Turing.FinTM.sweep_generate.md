<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.sweep_generate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterating a local generation rule

**Claim.** If each step from counter $i$ prepends the $i$th word symbol to the left list, drops the right-list head, and advances the coordinate by $d$, then after $n\leq |w|$ steps the machine is at counter $n$, coordinate $z+dn$, with the first $n$ symbols prepended in reverse order and the first $n$ right-list entries dropped.

**Proof.** Induct on $n$. At zero steps, the counter, coordinate, lists, and configuration are unchanged. For the successor case, run for $n$ steps first using the induction hypothesis, then take one step using the assumed local rule at counter $n$. The coordinate updates from $z+dn$ to $z+d(n+1)$, and the list identities for taking a prefix show that the newly prepended symbol extends the reversed prefix by one. Dropping one more right-list entry gives the list with its first $n+1$ entries removed. The bound $n+1\leq |w|$ ensures the required word symbol exists. The passage from an $(n+1)$-step run to one step after an $n$-step run is the run successor identity (`runFrom_succ_eq_step'`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
