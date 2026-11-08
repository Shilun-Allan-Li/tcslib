<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.layer1Gate_truncateWidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-layer gate under truncation

**Claim.** For any depth circuit $C$ and natural number $w$, the first-layer gate type of the circuit obtained by truncating $C$ to width $w$ is the same as that of $C$.

**Proof.** Width truncation retains or removes first-layer terms and adjusts the later wiring, while its definition assigns the first-layer gate type directly from $C$. Hence the two gate types are equal.
