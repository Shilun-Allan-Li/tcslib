<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonBits_of_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Bits from the Final Symbol

**Claim.** If the last symbol of a Boolean word, interpreted as true for the empty word, is true, then the binary expansion of the natural number whose bits are given by the word read from right to left is exactly that word.

**Proof.** Induct on the word. The empty case follows directly from the binary expansion of zero. For a nonempty word $b::w$, first separate the case that $w$ is empty: the assumption forces the single bit to be true, and the claim follows by evaluating its binary value. Otherwise write the tail as $c::w'$. The final-symbol condition then passes to this nonempty tail, so the induction hypothesis says that the binary expansion of its value is the tail itself. This tail value is nonzero: if it were zero, its binary expansion would be empty, contradicting that it equals the nonempty tail. The binary expansion theorem for appending a low-order bit to a nonzero number now gives the expansion of the full value as $b::(c::w')$, as required.
