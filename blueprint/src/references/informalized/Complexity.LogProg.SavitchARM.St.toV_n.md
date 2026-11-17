<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Counter Coordinate

**Claim.** For any register state, the coordinate of its register vector at the input-counter index is the state's input-length counter.

**Proof.** The register vector lists the state coordinates in order, placing $n$ at index $0$. The input-counter index is $r_n=0$, so the vector's value there is $n$.
