<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneSide_cascadeRight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rightward Cascade Preserves Side Words

**Claim.** Under the stated fullness, emptiness, donor, and room hypotheses, cascading rightward through zone $j$ prepends the home value to the concatenated left lists and removes the first entry of the concatenated right lists.

**Proof.** Proceed by induction on $j$, allowing the configuration to vary. For $j=0$, the room bound gives space for one additional entry in the left list at index $0$, since $2^{0-1}=1$ under natural-number subtraction. The cascade reduces to a single rightward move, and the side-word update follows from the rightward-move concatenation formula (`zoneSide_moveRight`).

For the successor case, write the target as $j+1$. First perform the outermost adjacent shift pair at indices $j$ and $j+1$. Because the right list at $j$ is empty and the left list there is full, and because the list at $j+1$ has the required room, the active-shift formula (`zoneStepPair_active`) says that the first $2^j$ entries of the right donor move to index $j$, while the first $2^j$ entries of the full left list at $j$ move to index $j+1$. The shift pair preserves each side's total concatenation (`zoneStepPair_side`).

The donor remains nonempty after this shift: its new list at $j$ is the first $2^j$ entries of a nonempty list, so it has positive length. The new left list at $j$ has length exactly $2^j$, using fullness of the old list and the capacity formula. This length satisfies the room bound needed to apply the induction hypothesis at level $j$, since $2^{j-1}\le 2^j$ and the capacity at $j$ is $2\cdot2^j$. At every index below $j$, the outer shift pair leaves both lists unchanged by the frame property (`zoneStepPair_frame`), so the emptiness and fullness hypotheses persist.

Apply the induction hypothesis to this shifted configuration. The cascade recursion (`zoneCascadeRight_succ`) expresses the level-$j+1$ cascade as the outer shift pair applied after the level-$j$ cascade on the shifted input. Both shift pairs preserve side words, so substituting the induction conclusion yields the claimed prepending on the left and tail on the right.

**Key facts.** `Turing.zoneSide_moveRight`, `Turing.zoneStepPair_active`, `Turing.zoneStepPair_frame`, `Turing.zoneStepPair_side`, `Turing.zoneCascadeRight_succ`.
