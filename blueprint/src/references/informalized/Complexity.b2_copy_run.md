<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_copy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a prefix under a choice word

**Claim.** If $i+|w|\le |x|$, running the host on choice word $w$ from copy state at position $i+1$, with $x$'s first $i$ symbols on the assembly buffer, ends in copy state at position $i+|w|+1$, with the first $i+|w|$ symbols on that buffer.

**Proof.** Induct on the choice word $w$, keeping the starting index $i$ general. For the empty word, the run does not change the configuration, and the asserted position and prefix are the initial ones. For a nonempty word $w=b::w'$, the bound implies $i<|x|$, so the one-step copying property (`b2_copy_step`) applies to the first bit. It advances the input head from $i+1$ to $i+2$ and extends the copied prefix from length $i$ to length $i+1$. The remaining word $w'$ has $i+1+|w'|\le |x|$, so the induction hypothesis applies starting at index $i+1$. It advances by the remaining length and establishes the claimed final position and copied prefix.

**Key facts.** `Turing.NDTM.runWith_cons`, `Complexity.b2_copy_step`.
