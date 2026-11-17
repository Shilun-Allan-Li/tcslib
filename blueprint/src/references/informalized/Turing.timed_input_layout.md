<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_input_layout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nested Input Layout

**Claim.** The nested pair encoding of $b$, $\alpha$, and $x$ consists of the clock prefix for $b$, followed by the pair encoding of $\alpha$ and $x$.

**Proof.** Induct on the word $b$. For the empty word, expanding the pair encodings and the clock prefix gives the same fixed delimiter followed by the encoding of $\alpha$ and $x$. For a word with first bit $c$ and tail $b'$, the induction hypothesis identifies the tail’s nested encoding with the clock prefix for $b'$ followed by the encoding of $\alpha$ and $x$. The outer pair encoding duplicates $c$ twice, and the inner encoding duplicates each of those two bits, so the initial block is four copies of $c$. This is exactly the first block contributed by the clock prefix; appending the induction-hypothesis identity gives the claimed layout.
