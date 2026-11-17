<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalInput_tag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary Tag from the Marker Tape

**Claim.** The Boolean tag defined from the single-marker tape is false at position zero and true at the right boundary; the claim imposes no restriction at interior positions.

**Proof.** The marker-tape read at a natural coordinate $p$ is `some true` exactly when $p=0`, and is blank otherwise (`Turing.universal_marker`). The tag is the decision that this read is not `some true`. At $p=0$ this decision is false; at the right boundary $p=n+1$, which is positive, the read is blank and the decision is true. These are the two required implications; no interior case is needed.

**Key facts.** `Turing.universal_marker`.
