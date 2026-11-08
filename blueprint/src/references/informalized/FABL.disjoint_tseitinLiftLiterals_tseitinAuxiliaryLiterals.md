<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.disjoint_tseitinLiftLiterals_tseitinAuxiliaryLiterals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Lifted and Auxiliary Coordinates

**Claim.** The coordinate indices of the lifted term literals are disjoint from those of the auxiliary literals for clause $k$.

**Proof.** Suppose an index occurs in both lists. An original literal with index $a\in\mathrm{Fin}(n)$ and an auxiliary position $p\in\mathrm{Fin}(b)$ then give the same coordinate in $\mathrm{Fin}(n+bc)$. Under the sum decomposition of this coordinate range, the lifted index is the image of the left summand containing $a$, while the auxiliary index is the image of the right summand containing the block coordinate determined by $(p,k)$. Injectivity of the sum-to-index equivalence would make these two sum elements equal. But elements in opposite summands cannot be equal. Thus no index occurs in both lists, proving disjointness.
