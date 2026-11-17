<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean :: Complexity.LogProg.SavitchARM.reflTransGen_of_reach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Gives Reflexive Transitive Reachability

**Claim.** Any pair related by the recursively defined reachability relation at any level is connected by a finite sequence of $R$-steps, allowing a sequence of length zero.

**Proof.** Induct on the level. At level zero, reachability means either the endpoints are equal, yielding a sequence of length zero, or they satisfy $R$, yielding one step. At a successor level, the definition supplies an intermediate point and reachability at the preceding level on both sides. By induction these give reflexive transitive paths from the first endpoint to the intermediate point and from there to the second. Concatenating the paths gives the required finite sequence.
