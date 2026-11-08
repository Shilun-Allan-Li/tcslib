<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Randomized.RTIME_subset_BPTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Time Is Bounded-Error Time

**Claim.** For every time bound $T$, $\mathrm{RTIME}(T)\subseteq\mathrm{BPTIME}(T)$.

**Proof.** Take $L\in\mathrm{RTIME}(T)$, witnessed by a constant $c$, a finite randomized machine $N$, and a randomized time-deciding property at bound $n\mapsto cT(n)$. The fact that every such randomized decider is a bounded-error decider (`RDecidesInTime.bpDecidesInTime`) gives the bounded-error property for the same machine and time bound. The same witness constant and machine establish $L\in\mathrm{BPTIME}(T)$.

**Key facts.** `Turing.FinNDTM.RDecidesInTime.bpDecidesInTime`.
