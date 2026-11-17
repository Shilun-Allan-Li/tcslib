<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Input_meaning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Meaning of the Input Clause Group

**Claim.** Under an assignment agreeing with a Boolean word $y$ on its first $m$ positions, the input clause group at time $t$ is satisfied exactly when the raw block's input slice is the two-bit code for the symbol read from $y$, with blank symbols at the boundary positions.

**Proof.** The input-symbol lookup lemma (`clA5InputBit`) expresses the symbol at position $p$ as the bit at index $p-1$ when $1\le p\le |y|$, and as blank otherwise. Since $|y|=m$, split according to whether the machine's input position lies in that range. In the in-range case, the input group is the present-symbol template. Its evaluation characterization (`clA5Group_eval`) says that satisfaction is equivalent to the raw block's input slice matching the code of the bit supplied by the assignment at index $p-1$. The assignment agrees there with $y$, so this is precisely the code of the symbol read from $y$. In the out-of-range case, the group is the absent-symbol template; the same evaluation characterization says its slice must match the blank-symbol code. These are exactly the two cases of the claimed equivalence.

**Key facts.** `Complexity.clA5InputBit`, `Complexity.clA5Group_eval`.
