<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.majorityThreePairValue_permutation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Rule and Coordinate Majority

**Claim.** For pairwise distinct indices $i,j,k\in\{0,1,2\}$ and signs assigned by $v$, the rule returning $v(i)$ if $v(i)=v(j)$ and $v(k)$ otherwise equals the majority of the three assigned signs.

**Proof.** The pairwise distinct indices $i,j,k$ exhaust the three elements of $\{0,1,2\}$. Consequently, the three entries of $v$ are exactly the signs being compared by the pair rule. Each is $1$ or $-1$. If $v(i)=v(j)$, that repeated sign is the majority; if they differ, the third sign agrees with one of them and is the majority. In either case the pair rule equals the majority of the entries of $v$.
