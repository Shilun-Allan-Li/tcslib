<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.capOf_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cap of an Appended Bit

**Claim.** Appending an optional Boolean value to a Boolean word changes its cap exactly by the cap-push operation.

**Proof.** If the optional value is absent, appending it adds no entries, and cap-push leaves the cap unchanged. If it is present, split the original word by its length. An empty word becomes a singleton, whose cap records that bit. A singleton becomes a word of length two, whose cap records that the length is at least two. A word already of length at least two remains in that same case after appending, so its cap remains the length-at-least-two marker. These are precisely the cases in the cap-push definition.
