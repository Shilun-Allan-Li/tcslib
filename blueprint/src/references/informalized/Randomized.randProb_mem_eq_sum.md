<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_mem_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Finite Set of Outputs

**Claim.** For a map $g$ from Boolean words to nonnegative integers and a finite set $T$, the probability that $g$ takes a value in $T$ is the sum, over $j\in T$, of the probabilities that $g=j$.

**Proof.** Induct on the finite set $T$. For the empty set, membership is always false, so the probability is zero (`Randomized.randProb_false`). For the inductive step, write the set as $\{a\}\cup T$, with $a\notin T$. The event that $g$ belongs to this union is the disjoint union of the events $g=a$ and $g\in T$: they cannot both occur, since that would put $a$ in $T$. The probability of a disjoint union is the sum of the two probabilities (`Randomized.randProb_or_disjoint`). The induction hypothesis expands the second term, and the finite-sum rule for adjoining a new element gives the desired sum over the union.

**Key facts.** `Randomized.randProb_false`, `Randomized.randProb_or_disjoint`.
