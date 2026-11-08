<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.setIndicator_binaryAffineSubspace_eq_translate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translation of an Affine Subspace Indicator

**Claim.** For every $x$, the indicator of $a+H$ at $x$ equals the indicator of $H$ at $x+a$.

**Proof.** Fix $x$ and split into whether $x$ belongs to the affine subspace. If it does, the membership criterion for an affine subspace says that $x+a\in H$ (`mem_binaryAffineSubspace_iff_add_mem`), so both indicators are $1$. If it does not, then $x+a\notin H$: otherwise the reverse implication of that same criterion would put $x$ in the affine subspace. Both indicators are therefore $0$. Since the values agree for every $x$, the functions agree.

**Key facts.** `FABL.mem_binaryAffineSubspace_iff_add_mem`.
