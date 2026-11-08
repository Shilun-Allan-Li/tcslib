<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecOneHot_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the One-Hot Encoding

**Claim.** The one-hot CNF encoding evaluates to true exactly when some $j\in\alpha$ is the unique selected element, meaning $a(i)$ is true exactly when $i=j$.

**Proof.** The encoding evaluates to true precisely when at least one element is selected and, for every pair of distinct elements, at least one of the two is unselected. Indeed, the first clause expresses the existence of a selected element, while each pair clause imposes the stated exclusion. Suppose these conditions hold, and choose a selected element $j$. Every $i\ne j$ must be unselected by the pair condition applied to $j,i$; hence $a(i)$ is true exactly when $i=j$. Conversely, if such a $j$ exists, then $j$ is selected, and among any two distinct elements at least one differs from $j$ and is therefore unselected. Both the existence clause and every pair clause hold, so the encoding evaluates to true.
