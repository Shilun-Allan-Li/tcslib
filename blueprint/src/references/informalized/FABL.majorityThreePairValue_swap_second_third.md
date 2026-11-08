<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.majorityThreePairValue_swap_second_third -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Input Majority After a Swap

**Claim.** For any three signs $a,b,c\in\{-1,1\}$, the pair rule applied to $a,c,b$ equals the majority of the vector whose entries are $a,b,c$ in that order.

**Proof.** Check the eight possible triples. If $a=c$, the pair rule applied to $a,c,b$ returns $a$, the repeated sign and hence the majority. If $a\ne c$, then $b$ must agree with one of them, and the rule returns $b$, again the majority. The majority is unaffected by listing these same three signs in the order $a,b,c$.
