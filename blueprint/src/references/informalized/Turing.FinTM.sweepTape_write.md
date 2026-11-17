<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing at the zipper frontier

**Claim.** Overwriting the represented tape at coordinate $z$ with $b$ gives the tape represented by the same frontier and left stack, with right stack $b$ prepended to the tail of $r$.

**Proof.** Compare the two tapes at an arbitrary coordinate $p$. If $p=z$, the tape reads the head of the right stack, so updating its value to $b$ agrees with reading the head of $b::r.tail$. This uses the frontier-read identity (`sweepTape_read`). If $p\ne z$, the update leaves the value unchanged. For $p<z$, both representations read from the same left stack. Otherwise $p>z$, and the right-stack index is positive: the entry of $b::r.tail$ at that index is precisely the entry of $r$ at the original index. This remains true when $r$ is empty, since both lookups are blank beyond the available list. Thus the tapes agree at every coordinate.

**Key facts.** `Turing.FinTM.sweepTape_read`.
