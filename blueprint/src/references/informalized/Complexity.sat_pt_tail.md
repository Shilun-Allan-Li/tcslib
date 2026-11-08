<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time List Tail

**Claim.** The function that removes the first bit from a binary string, returning the empty string when the input is empty, is polynomial-time computable.

**Proof.** Use the polynomial-time construction for mapping a finite-state process over a word to its emitted output (`satMap_poly`). Choose a one-state process that stays in its state, emits no bit while reading the first input bit, and emits the bit it reads on every subsequent position. Its output is the tail: on the empty list it emits nothing; on a nonempty list it skips the head and copies the remaining bits. Formally, induction on the input list shows that the process which emits on every position outputs the original list; splitting into empty and nonempty inputs then gives that the chosen process outputs the tail.

**Key facts.** `Complexity.satMap_poly`.
