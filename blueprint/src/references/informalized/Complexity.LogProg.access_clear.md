<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_clear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing a Work Tape

**Claim.** Under the stated head bounds and $n\le |y|+1$, the access machine can clear tape $0$ from its binary representation of $n$ and enter the exit state determined by $e$, with every step starting at a configuration satisfying the head bounds.

**Proof.** Use the clearing-run result (`clr_run`) on tape $0$. It supplies a finite run from the clearing state with the binary word for $n$ to the next state with tape $0$ holding the binary representation of zero, and bounds the moving head between $-1$ and the bit-length of $n$ at every earlier time. Since $n\le |y|+1$, monotonicity of bit-length (`length_bits_mono`) bounds that head by the global bit-length of $|y|+1$. All other heads remain within bounds by the frame property (`access_frame`), applied to the assumed-safe configuration $c$. Converting the run into an access path (`accessPath_of_run`) yields the required finite sequence. The binary representation of zero is empty (`Nat.zero_bits`), so the final tape content is blank, as claimed.

**Key facts.** `Complexity.LogProg.clr_run`, `Nat.zero_bits`, `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.access_frame`, `Complexity.LogProg.accessPath_of_run`.
