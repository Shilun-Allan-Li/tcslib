<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.drop_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Words and Final Bits

**Claim.** For every Boolean word $w$, its last bit with default value true is true exactly when $w$ is empty or its actual last bit is true; equivalently, this holds exactly when $w$ is canonical.

**Proof.** Split into the empty and nonempty cases. If $w$ is empty, its default last bit is true, and the defining condition for being canonical is vacuous. If $w$ is nonempty, the defaulted last bit is the actual last bit. Thus it equals true precisely when every nonemptiness witness gives that last bit as true, which is exactly the definition of canonicality.
