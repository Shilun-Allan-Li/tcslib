<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStepPair_active -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Active Paired Zone Shift

**Claim.** Under the stated emptiness, full-capacity, and available-room hypotheses, the paired shift redistributes the four affected left and right zone words as specified.

**Proof.** The paired shift first shifts words inward and then shifts words outward. Under the hypotheses, the relevant inward-shift condition and outward-shift capacity condition hold, so the definitions select their active branches. The inward shift splits each word at zone $i+1$ after its first $2^i$ entries. The outward shift takes the first $2^i$ entries of the full left word at zone $i$ into the left word there, and appends the remainder of that word to the left word at zone $i+1$. On the right, the empty word at zone $i$ receives the first $2^i$ entries from zone $i+1$, whose right word retains the remainder. These are exactly the four asserted equalities.
