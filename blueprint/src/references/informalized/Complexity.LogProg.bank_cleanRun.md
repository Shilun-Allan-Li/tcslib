<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean :: Complexity.LogProg.bank_cleanRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space-Bounded Clean Simulation of a Machine Bank

**Claim.** For each selected machine in the finite bank and each input, the bank machine halts with the bit indicating membership in that machine's language, has blank work tapes and heads reset to the origin, and keeps all head positions within the stated space bound throughout its run.

**Proof.** Fix the selected index $j$ and input $V$. The space-decider hypothesis supplies a time $T$ at which $M_j$ halts with the membership-indicator output, and bounds the total space it uses by $s_j(|V|)$ (`computesInTime_iff`). Let $K$ be the maximum number of work tapes among the machines in the bank. Since $M_j$ has at most $K$ tapes (`le_bankK`), it can be padded to $K$ tapes without changing its run. The machine that combines the bank's machines into a single machine likewise follows the selected machine's run: this follows by the run correspondence for the combined machine and the padding correspondence (`sigmaTM_runFrom`, `padTM_runFrom`). Thus the combined machine halts at time $T$.

For each of the first $(M_j).k$ tapes, the visited head positions in the combined run are exactly those of $M_j$. The number of such positions is bounded by the total space used by $M_j$, hence by $s_j(|V|)$ (`spaceUsedByTape_le_spaceUsed`). Each extra padded tape has its head fixed at the origin, so it visits at most one position. Therefore every tape in the combined run visits at most $\max(s_j(|V|),1)$ positions.

Apply the cleaning theorem to this combined machine and its halting run. It gives a cleaned run that halts with blank tapes, all heads at the origin, and every intermediate head position bounded by the same space bound (`cleanTM_run`). Its output is the combined machine's output at time $T$, which, by the run correspondences, is the selected decider's output: the single bit indicating whether $V\in A_j$. This is exactly the claimed clean run.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Complexity.LogProg.le_bankK`, `Complexity.LogProg.sigmaTM_runFrom`, `Complexity.LogProg.padTM_runFrom`, `Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed`, `Complexity.LogProg.cleanTM_run`.
