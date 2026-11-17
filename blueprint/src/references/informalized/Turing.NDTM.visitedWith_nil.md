<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean :: Turing.NDTM.visitedWith_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Position for an Empty Run

**Claim.** Under the empty choice word, the set of visited head positions on a chosen work tape is the singleton containing its initial head position.

**Proof.** For the empty word, the range used to define the visited positions is the range of $1$, so it contains only the index $0$. The prefix of length $0$ is empty, and running on it leaves the configuration unchanged. Hence the image of that range under the head-position map consists exactly of the initial head position, which is the asserted singleton.
