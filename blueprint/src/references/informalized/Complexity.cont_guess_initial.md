<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_guess_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration of the Guessing Phase

**Claim.** The guessing-phase machine’s initial configuration on $x$ is the invariant configuration built from $M$’s initial configuration on $x$ and the empty captured word.

**Proof.** Compare the configuration fields. The state and input position agree immediately: both are the initial state and the initial input-head position. For each work tape, split into the tapes belonging to $M$ and the additional capture tape. On an original tape the invariant configuration inherits the initial tape contents, which are blank, and its head position, which is zero. On the capture tape, the empty word gives blank contents everywhere and the head also starts at zero. The output is empty on both sides. Thus all components agree.
