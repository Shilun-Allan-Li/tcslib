<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_triple_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triple selection excludes the outer tapes

**Claim.** For either of the two outer tapes in the argument-and-capture pair, selection for a source tape is undefined at that outer tape's physical index.

**Proof.** Check the two possible component indices of the pair. The first is the initial outer tape, at physical index zero; the second is the final outer tape. Each lies outside the three index blocks assigned to the source tape's data, visited-marker, and origin-marker tapes. Thus none of the equalities tested by selection holds, and the result is undefined.
