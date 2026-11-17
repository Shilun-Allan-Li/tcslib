<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_cleanup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cleanup after reading

**Claim.** Starting in phase $rw_1(a)$ with tape $s$ holding the binary representation of $k$, the reading program reaches the exit state carrying $a$, with input head at position $1$ and the head of tape $s$ at $0$. Every earlier configuration lies in the read frame of $c$.

**Proof.** First apply the rewind property to the input head: the program moves left in phases $rw_1(a)$ and $rw_2(a)$ until it reaches the left boundary, then moves right once and enters $cR(a)$ at input position $1$. This gives a finite run and ensures that every configuration in this part remains a read-phase configuration with the required input-head behavior (the rewind property, `rewind_x`). The configurations produced by `readAt` are in the read frame (`readFrame_at`). From $cR(a)$, the program scans tape $s$ to its end, then returns across it while erasing its symbols; the clearing-run property (`clr_run`) shows that this finishes at the exit state carrying $a$, with tape $s$'s head at $0$. During this return, its head position stays between $-1$ and the length of the binary representation of $k$. Since $k\le |x|$, monotonicity of binary-word length bounds this by the frame's allowed limit (`length_bits_mono`). Concatenate the two runs using the run-addition law (`rrun_add`). Before the first run ends, use the rewind frame bound; afterward, use the clearing-run bound together with the binary-length estimate. Thus every configuration strictly before the combined endpoint lies in the read frame.

**Key facts.** `Complexity.LogProg.rewind_x`, `Complexity.LogProg.clr_run`, `Complexity.LogProg.rrun_add`, `Complexity.LogProg.readFrame_at`, `Complexity.LogProg.readFrame_reg`, `Complexity.LogProg.length_bits_mono`.
