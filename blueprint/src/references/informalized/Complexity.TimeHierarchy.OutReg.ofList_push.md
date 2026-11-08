<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.OutReg.ofList_push -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Register Under Appending

**Claim.** For every finite Boolean word $w$ and optional Boolean symbol $o$, the register of the word formed by appending $o$ to $w$ is obtained by pushing $o$ onto the register of $w$.

**Proof.** If $o$ is absent, appending its empty list changes neither the word nor its register, and pushing no symbol also leaves the register unchanged. If $o=b$ is present, split by the length of $w$. For the empty word, appending $b$ gives the one-symbol word and the push changes the empty register to the one-$b$ register. For a one-symbol word, appending $b$ gives a word of length two, whose register is many; pushing onto a one-symbol register also gives many. For a word of length at least two, its register is already many, and both the appended word's register and the pushed register remain many.
