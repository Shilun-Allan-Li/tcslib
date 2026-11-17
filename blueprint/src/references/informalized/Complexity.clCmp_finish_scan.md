<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_finish_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Scan Boundary Transition

**Claim.** At the maximum word width, one comparator step enters the rewind control carrying the final verdict, moves every work-tape head back one position, and leaves the input position, tape contents, and output unchanged, including when all four words are empty.

**Proof.** Let $m$ be the maximum word length. Since $m$ bounds that maximum, the common-boundary fact says that every work tape reads blank at position $m$ (the equivalence between all four reads being blank and the maximum length being at most the position, `Complexity.clCmp_blank`). The comparator's scanning transition therefore takes its blank-read branch: it enters the rewind control with the verdict computed from the accumulated scan state and moves each work-tape head one position left. The input-head movement is zero, so its position is unchanged (`Turing.moveInputPos_zero`). No symbols are written and no output is produced, so the words and output are unchanged. The same reasoning applies when $m=0$, since the boundary fact includes that case. The identification of the symbols read at the aligned heads with the words' symbols at position $m$ is supplied by `Complexity.clCmp_read`.

**Key facts.** `Complexity.clCmp_blank`, `Complexity.clCmp_read`, `Turing.moveInputPos_zero`.
