<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.notHaltedProb_rhoCoinRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting Probability for the Coin Run

**Claim.** For every infinite binary sequence $p$ and natural number $K$, the probability that the coin-run procedure does not halt on a uniformly random length-$K$ string is $(1/2)^K$.

**Proof.** Induct on $K$, allowing the sequence $p$ to vary in the induction hypothesis. At length zero, the empty input makes the procedure return no output, so the event is certain and has probability one (`Randomized.randProb_true`).

For the inductive step, split a length-$(K+1)$ input into its first bit and its remaining $K$ bits. If the first bit disagrees with $p(0)$, the procedure halts immediately, so that branch contributes zero (`Randomized.randProb_false`). If it agrees, the procedure continues on the suffix using the shifted sequence $i\mapsto p(i+1)$; the induction hypothesis says that the suffix fails to halt with probability $(1/2)^K$. The two first-bit branches have equal weight, as expressed by the one-bit probability decomposition (`Randomized.randProb_succ`). Consequently the total is one half of $(1/2)^K$ plus one half of zero, namely $(1/2)^{K+1}$. The identifications of the branch events use equality of the corresponding predicates on each string (`Randomized.randProb_congr`).

**Key facts.** `Randomized.randProb_true`, `Randomized.randProb_congr`, `Randomized.randProb_false`, `Randomized.randProb_succ`.
