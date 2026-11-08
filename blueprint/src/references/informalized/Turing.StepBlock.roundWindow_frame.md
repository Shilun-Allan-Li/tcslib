<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundWindow_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the Round Window

**Claim.** If the input head and first $k$ work-tape heads of $d$ each occupy one of their two allowed positions, then a configuration $e$ with those same head positions satisfies the same alternatives.

**Proof.** The round-window hypothesis gives the two allowed alternatives for the input head and, separately, for each of the first $k$ work-tape heads. The assumed equalities identify the corresponding positions of $e$ with those of $d$. Substituting these equal positions preserves each disjunction, which is precisely the round-window condition for $e$.
