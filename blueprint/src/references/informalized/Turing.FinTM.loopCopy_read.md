<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopCopy_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading at the Copying Frontier

**Claim.** At cell $|p|$, the copying tape storing the concatenation of $p$ and $r$, while blanking the processed prefix, reads the first symbol of $r$, or blank if $r$ is empty.

**Proof.** At the frontier cell $|p|$, the cell is not below the processed-prefix length, so the copying tape returns the buffer value of $p$ followed by $r$ at position $|p|$. The frontier-read fact for buffers identifies this value with the head of $r$ (Turing.FinTM.loopBuffer_read).

**Key facts.** `Turing.FinTM.loopBuffer_read`.
