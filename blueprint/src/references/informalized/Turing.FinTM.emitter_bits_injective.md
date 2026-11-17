<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_bits_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Binary Representation

**Claim.** The map sending a natural number to its binary digit word is injective.

**Proof.** For every natural number $n$, folding its binary digit word with the binary accumulation operation reconstructs $n$. This reconstruction identity follows by binary recursion: it holds at zero, and the recursion step follows from the identity describing the digit word of a number formed by appending a binary bit. If two numbers have the same digit word, applying this fold to both sides gives the same reconstructed number; hence the original numbers are equal.
