<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeBlockCoordinates_union_ordered -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordered Three-Block Cover

**Claim.** For pairwise distinct $a,b,c\in\mathrm{Fin}(3)$, the union of the coordinate blocks indexed by $a$, $b$, and $c$ at level $1$ is all of $\mathrm{Fin}(3^2)$.

**Proof.** Because $a,b,c$ are pairwise distinct elements of the three-element set $\mathrm{Fin}(3)$, they are precisely its three elements, in some order. The three blocks are therefore the same collection of blocks as those indexed by $0,1,2$. Their union covers all coordinates by the three-block covering result ($\texttt{FABL.recursiveMajorityThreeBlockCoordinates_union}$).

**Key facts.** `FABL.recursiveMajorityThreeBlockCoordinates_union`.
