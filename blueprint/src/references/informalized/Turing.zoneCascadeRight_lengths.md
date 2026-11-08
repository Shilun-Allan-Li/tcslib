<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneCascadeRight_lengths -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zone Lengths After a Rightward Cascade

**Claim.** Under the stated emptiness, fullness, donor-length, and capacity assumptions, the rightward cascade leaves both words at each lower level $k<j$ with length $2^k$; at level $j$ it transfers $2^j$ symbols from the right word to the left word.

**Proof.** Induct on $j$, allowing the zone contents to vary. At $j=0$, the room assumption permits the single rightward move at level zero. It removes one symbol from the right word and adds one to the left word, which gives the asserted top-level lengths; there are no lower levels to check. For $j+1$, first use the active paired-shift calculation (`zoneStepPair_active`) at level $j$: the empty right word and full left word there cause the shift to split off the first $2^j$ symbols from the donor at level $j+1$. The lower words remain unchanged by the frame property (`zoneStepPair_frame`). The list lengths of the resulting prefixes, suffixes, and concatenation show that level $j$ now has a donor of length $2^j$ and a left word of length $2^j$, while level $j+1$ has lost $2^j$ symbols on the right and gained $2^j$ on the left.

Apply the induction hypothesis to the first $j$ levels of these intermediate contents. Its hypotheses hold because the lower right words are still empty and the lower left words still full; the new level-$j$ donor and left lengths are both $2^j$. The induction conclusion makes the level-$j$ right word empty and its left word full, and establishes the desired lengths below it. The frame property says this inner cascade does not alter level $j+1$, so the intermediate top-level length changes persist. The successor decomposition then applies one final paired shift at level $j+1$ (`zoneCascadeRight_succ`). The active-shift calculation now transfers another $2^j$ symbols: its take and drop lengths give the lower level-$j$ words length $2^j$, and the top-level net transfer is $2\cdot 2^j=2^{j+1}$. The capacity and donor assumptions ensure these lengths are valid, completing the induction.

**Key facts.** `Turing.zoneStepPair_active`, `Turing.zoneStepPair_frame`, `Turing.zoneCascadeRight_frame`, `Turing.zoneCascadeRight_succ`.
