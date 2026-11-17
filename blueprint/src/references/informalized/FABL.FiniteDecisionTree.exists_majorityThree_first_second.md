<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.FiniteDecisionTree.exists_majorityThree_first_second -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Lower Bound for Three-Bit Majority

**Claim.** For any decision tree computing majority on three signs, one can choose a first coordinate $i$ and, for each sign $a$, a different coordinate $j(a)$ such that every input requires at least two queries, and at least three when $x_i\ne x_{j(x_i)}$.

**Proof.** The query-skeleton theorem supplies a root query at some coordinate $i$. For each possible root value $a$, it supplies a second query at some coordinate $j(a)$, and after any different value $b$ at that query, it supplies a third query. Since $j(a)$ is available only after erasing $i$, it differs from $i$. On input $x$, the root and second query therefore already contribute two queries. If $x_i=x_{j(x_i)}$, this gives the stated lower bound of two. Otherwise, the second query receives a value different from the root value, so the skeleton guarantees a third query on that branch. The total is then at least three, as required.

**Key facts.** `FABL.FiniteDecisionTree.exists_majorityThree_querySkeleton`.
