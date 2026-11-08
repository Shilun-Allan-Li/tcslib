<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/Restrictions.lean :: FABL.liftFreeFrequencyPart_union_liftFixedFrequencyPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposition of a finite index set

**Claim.** For subsets $J,U$ of $\mathrm{Fin}(n)$, the elements of $U$ lying in $J$ and those outside $J$ form two parts whose lifted union is $U$.

**Proof.** Check membership for an arbitrary index $i$. If $i\in J$, then it appears in the part of $U$ indexed by $J$ exactly when $i\in U$; it cannot appear in the part indexed by elements outside $J$. If $i\notin J$, the first part cannot contain it, while the second contains it exactly when $i\in U$. In either case, membership in the union is equivalent to membership in $U$, so the finite sets are equal.
