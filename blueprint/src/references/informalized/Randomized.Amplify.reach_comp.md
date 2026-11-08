<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.reach_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Under Composed Runs

**Claim.** If every run of $N$ from $c$ maps to a configuration satisfying $P$, and $P$ persists through all further runs of $M$ from mapped halted configurations, then every run of $M$ from $\phi(c)$ satisfies $P$.

**Proof.** Induct on the choice word $w$. For the empty word, the reached configuration is $\phi(c)$, and the first hypothesis with the empty run gives $P$ directly. For a nonempty word $b::w$, if $c$ is halted, the second hypothesis applied to the empty run gives $P$ after the entire word. Otherwise, split off the first choice bit. The run equation (`runWith_cons`) expresses the remaining run as starting after that first step, and the assumed step correspondence identifies this successor of $M$ with the image of the corresponding successor of $N$. Apply the induction hypothesis to that successor, using the first premise for all prefixed runs $b::u$ and the second premise for their halted cases. This proves $P$ at the end of the original run.

**Key facts.** `Turing.NDTM.runWith_cons`.
