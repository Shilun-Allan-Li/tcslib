<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.toV_Q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scratch register coordinate

**Claim.** For a state of the Savitch machine, the coordinate at index $17$ in its 18-entry register vector equals the value of its scratch register $Q$.

**Proof.** The register vector lists $Q$ as its final entry, at index $17$. Since this is the index denoted by $r_Q$, evaluating the vector there gives $Q$ directly.
