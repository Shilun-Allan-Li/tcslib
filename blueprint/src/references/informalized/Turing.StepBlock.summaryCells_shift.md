<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.summaryCells_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Summary-Cell Values

**Claim.** For $z\ge-1$, the summary-cell content at position $2+z$ equals the buffer content of $w$ at position $z$.

**Proof.** Since $z\ge-1$, we have $2+z\ge1$, so this position is not zero. The summary-cell function therefore uses the buffer tape, at argument $(2+z)-2=z$, giving the asserted equality.
