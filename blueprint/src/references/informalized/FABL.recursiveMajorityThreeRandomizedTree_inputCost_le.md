<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeRandomizedTree_inputCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected query cost bound

**Claim.** For every natural number $d$ and every sign vector $x$ of length $3^d$, the expected query cost of the randomized recursive three-way majority tree on input $x$ is at most $(8/3)^d$.

**Proof.** We argue by induction on $d$. At depth zero, the tree makes exactly one query, so its expected cost is $1$, which equals the bound at depth zero (`recursiveMajorityThreeRandomizedTree_inputCost_zero`, `recursiveMajorityRandomizedCostBound_zero`).

Suppose the bound holds at depth $d$, and fix an input of length $3^{d+1}$. Split it into its three recursive blocks. Write $c_i$ for the expected cost of the depth-$d$ tree on block $i$, and $s_i$ for that block's recursive majority output. By the induction hypothesis, $c_i\le C$, where $C=(8/3)^d$, and each $c_i$ is nonnegative (`inputCost_nonneg`). The one-step cost formula says that the expected cost at depth $d+1$ is the average of the costs from the three orders $012$, $021$, and $120$: each order queries its first two blocks, and queries the third precisely when the first two outputs disagree (`recursiveMajorityThreeRandomizedTree_inputCost_succ`).

If all three outputs agree, each order stops after its first two blocks. Each $c_i$ therefore occurs twice in the sum of the three order costs, giving an average of $(2/3)(c_0+c_1+c_2)\le 2C$. Otherwise, exactly two outputs agree. For example, if $s_0=s_1\ne s_2$, order $012$ stops after its first two blocks, while orders $021$ and $120$ query all three. Thus the total across the three orders is $3c_0+3c_1+2c_2$, whose average is at most $(8/3)C$. The other choices of the agreeing pair give the same bound by the corresponding count of how often each block is queried. These cases establish the required successor bound, since the cost bound at depth $d+1$ is $(8/3)C$ (`recursiveMajorityRandomizedCostBound_succ`).

**Key facts.** `FABL.recursiveMajorityThreeRandomizedTree_inputCost_zero`, `FABL.recursiveMajorityRandomizedCostBound_zero`, `FABL.recursiveMajorityThreeRandomizedTree_inputCost_succ`, `FABL.RandomizedDecisionTree.inputCost_nonneg`, `FABL.recursiveMajorityRandomizedCostBound_succ`.
