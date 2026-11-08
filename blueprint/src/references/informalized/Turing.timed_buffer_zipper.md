<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_buffer_zipper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer Tape as a Zipper

**Claim.** For every Boolean word $b_s$, its buffer tape equals the zipper tape with frontier at $0$, empty processed stack, and unprocessed list consisting of the bits of $b_s$ in order.

**Proof.** Compare the two tapes at an arbitrary integer position $z$. If $z\ge0$, the buffer tape reads the $z$th entry of $b_s$ (when present); the zipper tape reads the $z$th entry of the unprocessed list $b_s.\mathrm{map}(\mathrm{some})$, and joining that optional value recovers the same bit or blank. If $z<0$, the buffer tape is blank by definition, and the zipper tape is also blank because its processed stack is empty. Thus the tapes agree at every position.
