<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.RTIME_subset_NTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Time Is Nondeterministic Time

**Claim.** For every time bound $T$, $\mathrm{RTIME}(T)\subseteq\mathrm{NTIME}(T)$.

**Proof.** Let $L\in\mathrm{RTIME}(T)$, with witnesses a constant $c$ and a finite machine $N$ that randomized-decides $L$ within time $cT$. A randomized time decider is also a nondeterministic time decider with the same time bound (`RDecidesInTime.decidesInTime`). Hence the same witnesses show that $L\in\mathrm{NTIME}(T)$.

**Key facts.** `Turing.FinNDTM.RDecidesInTime.decidesInTime`.
