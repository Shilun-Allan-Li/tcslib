<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.totalInfluence_le_decisionTreeSizeInfluenceBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound from Decision Tree Size

**Claim.** For a monotone Boolean function whose deterministic decision tree has size at most $n^d$, total influence is at most $\sqrt{d\,\operatorname{clog}_2(n+1)}+1$.

**Proof.** Let $s$ be the deterministic decision tree size and $L=\operatorname{clog}_2(n+1)$. A tree computing the function and having exactly $s$ leaves exists, and every such tree has at least one leaf (`FABL.FiniteDecisionTree.exists_computingTree_leafCount_eq_deterministicSize`, `FABL.FiniteDecisionTree.leafCount_pos'`), so $s>0$. From $s\le n^d\le(n+1)^d\le(2^L)^d=2^{dL}$, it follows that $\operatorname{clog}_2(s)\le dL$, and hence $\log_2 s\le dL$. The monotone decision-tree influence estimate gives total influence at most $\sqrt{\log_2 s}$ (`FABL.totalInfluence_le_sqrt_logb_deterministicSize_of_monotone`), which is at most $\sqrt{dL}$. Finally, $\sqrt{dL}\le\lfloor\sqrt{dL}\rfloor+1$, yielding the stated integer-valued bound.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_leafCount_eq_deterministicSize`, `FABL.FiniteDecisionTree.leafCount_pos'`, `FABL.totalInfluence_le_sqrt_logb_deterministicSize_of_monotone`.
