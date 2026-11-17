<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCopy_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Copying Pass

**Claim.** For every input word, valid input-head position, source prefix and suffix, and record, running the copier for twice the suffix length from its reading control copies each suffix bit twice into the record, advances the source head to the end of the source word, and preserves the other stated configuration data.

**Proof.** Induct on the suffix $w$. If it is empty, the run has length zero, and the initial and claimed configurations agree. For the inductive step, write $w=b::v$. The two-step single-bit result (`clCopy_pair`) processes the first bit $b$: it appends $bb$ to the record and advances the source head by one, leaving the copier in its reading control. The remaining suffix is $v$, now read with prefix $u$ extended by $b$ and record extended by $bb$. Apply the induction hypothesis to those updated words. The run lengths add to $2+2|v|=2|w|$, and the appended record is exactly the result of replacing every bit of $w$ by two copies.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Complexity.clCopy_pair`.
