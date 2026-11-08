<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_branch_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Branch Configuration Head Positions

**Claim.** The work-head positions of the timed branch configuration are the concatenation of the supplied head vectors for $D$ and the branch machine, followed by the final position $0$.

**Proof.** Expand the definitions of the timed branch configuration and the conditional head vector. Both work-head functions are built by the same nested concatenation of the supplied vectors, with the final one-tape component constantly zero. Their values therefore agree at every tape index, so the functions are equal by reflexivity.
