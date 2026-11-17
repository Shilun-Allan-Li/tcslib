<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seam_ofWords_mapState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Renaming of a Word Configuration

**Claim.** Renaming the state of the word configuration for $q$ by $f$ gives the word configuration for $f(q)$ with the same family of words.

**Proof.** The word configuration stores the state as `some q` and its tape data, head positions, input position, and output are determined by the family of words. State renaming maps `some q` to `some (f q)` and preserves all other fields. These are exactly the fields of the word configuration for $f(q)$ and the unchanged word family, so the configurations are equal.
