<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.majorityThreePairValue_rotate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rotated Three-Input Majority

**Claim.** For any three signs $a,b,c\in\{-1,1\}$, the pair rule applied to $b,c,a$ equals the majority of the vector whose entries are $a,b,c$ in that order.

**Proof.** There are eight possible triples of signs. For each, the pair rule applied to $b,c,a$ returns the repeated sign when $b=c$; when $b\ne c$, it returns $a$, which agrees with exactly one of $b,c$ and is therefore the majority. This is precisely the majority of the same three signs listed as $a,b,c$, so the order does not change the result.
