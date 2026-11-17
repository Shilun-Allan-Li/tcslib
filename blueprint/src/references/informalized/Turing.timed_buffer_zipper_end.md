<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_buffer_zipper_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer tape as a processed zipper

**Claim.** For every Boolean word $b_s$, its buffer tape is the zipper tape with frontier at $|b_s|$, processed stack consisting of the bits of $b_s$ in reverse order, and empty unprocessed list.

**Proof.** First express the buffer tape as a sweep tape with frontier at $0$, empty processed stack, and the word $b_s$ (each bit wrapped as an optional symbol) still unprocessed; this is the buffer-to-zipper identity (`timed_buffer_zipper`). Then apply the sweep-shift identity with the entire word as the segment being moved across the frontier. It advances the frontier by the word's length, moves the reversed segment onto the processed stack, and leaves the unprocessed list empty. The resulting sweep tape is exactly the claimed one.

**Key facts.** `Turing.timed_buffer_zipper`, `Turing.timed_sweep_shift`.
