<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean :: Complexity.CPSim.ans_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answers Beyond the Output

**Claim.** If the output word $O$ has length at most $p$, then the answer function at position $p$ is false in either Boolean mode.

**Proof.** Split on the mode. In the mode that tests whether $p<|O|$, the length bound rules out that inequality, so the answer is false. In the mode that reads the $p$th list entry with default value false, the length bound places $p$ beyond the end of the list, where the default applies.
