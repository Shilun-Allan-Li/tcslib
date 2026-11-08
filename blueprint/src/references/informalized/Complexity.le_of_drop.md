<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean :: Complexity.le_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound after dropping a prefix

**Claim.** If dropping the first $p$ entries of $x$ leaves $u$ followed by $r$, and $u$ is nonempty, then $p+|u|\le |x|$.

**Proof.** Taking lengths in the equality $x.drop\ p=u++r$ gives $|x|-p=|u|+|r|$. Since $u$ is nonempty, $|u|>0$; in particular, $|u|+|r|\ge |u|$. Rearranging yields $p+|u|\le |x|$.
