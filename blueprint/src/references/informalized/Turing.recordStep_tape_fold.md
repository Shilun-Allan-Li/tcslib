<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_tape_fold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape Window Fold

**Claim.** For a configuration whose work-tape heads and contents lie within the window from $-s$ to $s$, folding the record symbols for tape $i$ in the forward direction and then applying the identity backward preserves the word and returns the head’s content and the two endpoint indicators.

**Proof.** By the scan identity (`Turing.scanResult_fold`), the scan leaves the record word unchanged and its summary is the left fold of `recordStepTapeFold` over that word. Write $p=(h_i+s)$, where $h_i$ is the head position. The window hypothesis gives $0\le p\le 2s$, so $p$ is an index in the word. At each index $j$, the mark condition $p=j$ is equivalent to $h_i=j-s$. Thus the word is exactly the prefix-fold input with its mark at the head index. The finite-prefix fold formula (`Turing.recordStep_tape_prefix`) says that this fold records the content at index $p$, and marks the first and last positions precisely when $p=0$ and $p+1=2s+1$. Since the cell at index $p$ is at position $h_i$, these are the content under the head and the endpoint equalities $h_i=-s$ and $h_i=s$, respectively.

**Key facts.** `Turing.scanResult_fold`, `Turing.recordStep_tape_prefix`.
