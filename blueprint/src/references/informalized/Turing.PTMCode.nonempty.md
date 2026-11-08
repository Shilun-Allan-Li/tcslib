<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPHard.lean :: Turing.PTMCode.nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a Machine Code

**Claim.** There exists a probabilistic Turing machine code whose decoding recovers each encoded machine even after any finite string of true bits is appended.

**Proof.** Choose an injective map $f$ from machine descriptions to natural numbers, available because the type of descriptions is countable. Encode a machine $M$ by the list of $f(M)$ false bits. Decode any binary list $s$ by counting its initial consecutive false bits and applying the inverse of $f$ to that count; the inverse is defined on all natural numbers, so this gives a total decoder. After appending any number of true bits to the encoding, the initial false-bit segment still has length $f(M)$: the first true bit, if present, ends that segment, and if no true bits are appended the whole list consists of false bits. Thus decoding returns the inverse of $f$ applied to $f(M)$, which is $M$ by injectivity.
