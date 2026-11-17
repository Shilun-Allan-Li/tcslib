<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean :: Complexity.CPSim.ans_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer Stability Under Appending Bits

**Claim.** If $p<|O|$, then the answer at position $p$ has the same value on $O$ and on $O$ concatenated with any bit string $e$, for either Boolean mode.

**Proof.** Split on the mode parameter. In the mode that tests whether $p$ is within the output length, the inequality $p<|O|$ remains true after appending $e$, since concatenation cannot shorten a list. In the mode that reads the bit at position $p$, an index already within $O$ has the same entry in $O$ and in $O$ concatenated with $e$. Hence the answer agrees in either mode.
