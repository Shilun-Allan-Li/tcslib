<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_increment_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix and optional separator decomposition

**Claim.** Every finite Boolean word is a run of true bits, followed optionally by one false separator, followed by a remaining word.

**Proof.** Induct on the word. The empty word has a decomposition with a run of length zero and no separator or remainder. If the first bit is false, choose a run of length zero and take the remaining tail as the optional word after the separator. If the first bit is true, decompose the tail by induction and increase its initial run length by one; adjoining that true bit gives the required decomposition.
