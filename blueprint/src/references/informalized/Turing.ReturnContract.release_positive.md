<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.ReturnContract.release_positive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Duration of the Release Contract

**Claim.** For a return contract $C$, every configuration satisfying its precondition and whose state is the anchor has strictly positive prescribed running time under the contract’s release.

**Proof.** Fix data $i$ and a configuration $d$ satisfying the release contract’s precondition and whose state is the anchor. The release construction maps configurations in a way that preserves the anchor state, so the given state equality implies that the mapped configuration is also in the anchor state. Apply the original return contract’s positivity property to that mapped configuration and the same precondition. Its prescribed time is exactly the release contract’s time, proving the required strict positivity.
