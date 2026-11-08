<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.expCost_bind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Cost of a Bind

**Claim.** For a probability mass function $p$ on $\gamma$ and a family of probability mass functions $f(a)$ on pairs $(b,n)$, the expected second coordinate after sampling first from $p$ and then from $f(a)$ is $\sum_a p(a)\,\mathbb{E}_{f(a)}[n]$, with sums and expectations in the nonnegative extended reals.

**Proof.** Expand the expected cost of the bound distribution as a sum over pairs $(b,n)$. The bind formula expresses the mass of each pair as the sum over $a$ of $p(a)$ times the mass assigned to that pair by $f(a)$. Reordering the resulting nonnegative double sum groups terms by $a$. Factoring the constant $p(a)$ out of the inner sum leaves exactly the expected cost under $f(a)$, giving the stated identity.
