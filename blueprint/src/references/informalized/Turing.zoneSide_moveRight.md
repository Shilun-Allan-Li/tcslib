<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneSide_moveRight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Side Words After a Rightward Move

**Claim.** When the index-zero left list has room for one more entry and the index-zero right list is nonempty, a rightward move prepends the home value to the left side word and removes the first entry of the right side word.

**Proof.** Split the concatenation at index $0$: for a list of $n+1$ zones, the side word is the list at index $0$ followed by the concatenation of all successor-index lists (`zoneSide_succ`). The move changes only the lists at index $0`; every successor-index list is unchanged. Thus the left side word becomes the old index-zero list with the home value prepended, followed by the unchanged remainder, giving the home value prepended to the original side word. For the right side, the new index-zero list is the tail of its old nonempty list, with the remaining indices unchanged. The tail of a concatenation with a nonempty first list is the tail of that first list followed by the unchanged remainder, which gives the asserted formula.

**Key facts.** `Turing.zoneSide_succ`.
