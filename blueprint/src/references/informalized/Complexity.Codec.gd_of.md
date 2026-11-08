<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.gd_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register bounds give the guard

**Claim.** If every register is at most $B$ and the configuration with label $l$, registers $v$, and no pending answer satisfies the codec precondition, then it satisfies the guard with bound $B.

**Proof.** The guard is the conjunction of the codec precondition and the assertion that every register is at most $B$. The precondition is the given hypothesis, and the register inequalities are exactly the other given hypothesis. Pairing them gives the guarded condition.
