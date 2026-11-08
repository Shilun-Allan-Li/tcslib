<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneSide_adjacent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacent Zone Concatenation

**Claim.** If the concatenations at two adjacent indices $a$ and $a+1$ agree for assignments $w$ and $v$, and the assignments agree at every other index, then their concatenations over all indices in order agree.

**Proof.** Proceed by induction on the number of indices, using the decomposition of a concatenation into its first word followed by the concatenation of the remaining indices (`zoneSide_succ`). If $a=0$, the assumed equality of the first two words together lets us group those words as one common prefix; all later words agree individually, so the full concatenations agree. If $a$ is positive, the first words agree because index $0$ is outside the designated adjacent pair. Remove that common prefix and apply the induction hypothesis to the remaining indices, where the pair has shifted down by one and its concatenation equality and all other pointwise agreements are preserved. This proves equality of the full concatenations.

**Key facts.** `Turing.zoneSide_succ`.
