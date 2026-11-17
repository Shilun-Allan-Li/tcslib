<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.OutReg.ofList_eq_one_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton True Output Recognition

**Claim.** For every finite Boolean word $w$, its output register is the singleton register for true exactly when $w=[true]$.

**Proof.** Split by the length of $w$. For the empty word, the register is empty, so it is not the singleton-true register. For a one-symbol word $[b]$, the register is the one-symbol register for $b$, which equals the one-true register exactly when $b=true$; this is precisely $[b]=[true]$. For a word with at least two symbols, the register is many, so it cannot equal the one-true register. These cases establish both directions.
