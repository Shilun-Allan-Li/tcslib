<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_tape_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape Fold on a Prefix

**Claim.** Folding the first $r$ record symbols, marking exactly the position $p$, returns whether the prefix is nonempty, the content at $p$ when it lies in the prefix (and none otherwise), and indicators for whether the first or last position is marked.

**Proof.** Proceed by induction on $r$. For $r=0$, the word is empty and the initial summary has all four entries in the claimed values. For the successor case, split the range into the first $r$ positions followed by the new position $r$. By the induction hypothesis, the first three summary entries describe the old prefix. If $p=r$, the new cell is the marked one: its content becomes the recorded content, and the endpoint indicators are determined by whether this is also position zero and whether it is the new last position. The special possibility $r=0$ is handled directly. If $p\ne r$, the new cell is unmarked, so the stored content and left-edge indicator remain as they were, while the right-edge indicator reflects whether the old prefix was empty at its boundary. In this case $p<r+1$ is equivalent to $p<r$. These cases give the stated summary.
