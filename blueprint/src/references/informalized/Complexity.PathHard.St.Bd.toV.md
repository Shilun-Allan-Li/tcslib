<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.St.Bd.toV -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State bounds imply coordinate bounds

**Claim.** If each of the fifteen coordinates of a state record is at most $B$, then every entry of its coordinate vector is at most $B$.

**Proof.** The hypothesis supplies one bound for each of the fifteen coordinates. Fix an index of the coordinate vector. Since it has fifteen possible indices, its entry is the corresponding state coordinate; the matching inequality from the hypothesis therefore bounds that entry by $B$.
