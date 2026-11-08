<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_cur -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Current walk code coordinate

**Claim.** For any state σ and natural number z, the register vector associated with σ has value cur at coordinate 15.

**Proof.** By definition, the register vector lists the fields of σ in order, with cur in position 15 when indexing starts at 0. The designated coordinate rcur is 15, so evaluating the vector there gives σ.cur directly. The number z does not affect this equality.
