<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrCfg_ctr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanned Counter Symbol

**Claim.** In a clock configuration formed from buffer tape $\tau$ with head position $z$, the symbol scanned on the distinguished buffer tape is $\tau(z)$.

**Proof.** The distinguished buffer tape is the middle block in the clock machine’s work tapes, and its head position is likewise $z$. Evaluating the tape contents at that head position therefore gives $\tau(z)`, as asserted.
