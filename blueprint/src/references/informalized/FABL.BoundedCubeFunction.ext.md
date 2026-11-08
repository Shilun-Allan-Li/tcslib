<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.BoundedCubeFunction.ext -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extensionality of bounded cube functions

**Claim.** Two bounded real-valued functions on the sign cube are equal as bounded cube functions whenever their underlying functions agree at every input.

**Proof.** The underlying functions agree by hypothesis. A bounded cube function is determined by its underlying function together with the proof that its values lie in $[-1,1]$; the latter is a proposition, so any two such proofs are equal. Hence the two structures are equal.
