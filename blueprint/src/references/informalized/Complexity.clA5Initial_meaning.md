<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Initial_meaning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Snapshot Characterization

**Claim.** Under the stated agreement between $a$ and the bits of $y$, the initial-template condition at time zero holds exactly when the raw time-zero block is the encoding of $M$’s initial snapshot on $y$.

**Proof.** The time-zero snapshot has the initial state, no work-tape symbols, and input read $\operatorname{inputBitAt}(y,1)$ (`snapshotAt_zero`). The boundary-aware input formula (`clA5InputBit`) says this read is absent if $y$ is empty and otherwise is the first bit of $y$. Split on whether $m>0$. If $m>0$, the template marks the input as present, and the hypothesis on $a$ at position zero identifies its bit with the first bit of $y$; hence the initial-template condition is precisely equality of the raw block with the encoding of that snapshot. If $m=0$, then $y$ is empty by $|y|=m$, the template marks the input absent, and the same equality follows with no input symbol. In both cases the two propositions are equivalent.

**Key facts.** `Complexity.snapshotAt_zero`, `Complexity.clA5InputBit`.
