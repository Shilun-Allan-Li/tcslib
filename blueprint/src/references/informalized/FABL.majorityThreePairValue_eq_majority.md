<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.majorityThreePairValue_eq_majority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Rule Gives Three-Sign Majority

**Claim.** For any three signs $a,b,c\in\{-1,1\}$, the rule returning $a$ when $a=b$ and returning $c$ otherwise agrees with their majority.

**Proof.** Each sign is either $1$ or $-1$, so there are eight cases. If $a=b$, the pair rule returns $a$, which occurs at least twice and is therefore the majority. If $a\ne b$, then the two signs are opposite; since $c$ is one of these two signs, it agrees with exactly one of them, and the majority is $c$. Thus the rule gives the majority in every case.
