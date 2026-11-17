<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_cond_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional machine space bound

**Claim.** If $D$ computes $[b]$ on $x$ in exactly $T$ steps, then the conditional machine's space through time $t$ is at most the space of $D$ through $T$, plus the selected branch's space through $t$, plus $2$.

**Proof.** For each tape belonging to $D$, the head-ledger lemma (\texttt{Turing.FinTM.f2_cond_ledger}) says that every position visited by that tape in the conditional computation equals a position visited by the corresponding tape of $D$ at some time at most $T$. Hence its visited-position set, and thus its space, is bounded by $D$'s. The same ledger shows that each tape belonging to the branch machine visits only positions visited on that branch by time at most $t$, since its branch-time index is at most the current time; these tape spaces are therefore bounded by the branch's. Finally, every visited position of the extra control tape lies in the integer interval $[0,1]$, again by the ledger, so this tape contributes at most two positions. The total space is the sum over all tapes. Splitting this sum into the detector tapes, branch tapes, and the single extra tape using the finite-sum decomposition lemma (\texttt{Turing.FinTM.f2_sum_add}) yields the claimed bound.

**Key facts.** `Turing.FinTM.f2_cond_ledger`, `Turing.FinTM.f2_sum_add`.
