<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.eval_permuteCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under coordinate permutation

**Claim.** Permuting a finite decision tree's coordinates by $\sigma$ and evaluating at $x$ gives the same output as evaluating the original tree at the input $i\mapsto x_{\sigma(i)}$.

**Proof.** Unfolding the coordinate permutation, the query at an original coordinate $i$ becomes a query at $\sigma(i)$. Thus, at input $x$, the permuted tree follows the child indexed by $x_{\sigma(i)}$. This is exactly the child the original tree follows when evaluated at the input whose value at $i$ is $x_{\sigma(i)}$. The same correspondence holds at every subsequent query, so both evaluations reach the same leaf and return the same label.
