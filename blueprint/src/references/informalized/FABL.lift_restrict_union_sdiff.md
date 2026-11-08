<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.lift_restrict_union_sdiff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction and set difference decomposition

**Claim.** The lifted restriction of $S$ to $J$, together with the elements of $S$ outside $J$, is exactly $S$.

**Proof.** Check membership for each ambient element $i$, splitting according to whether $i$ belongs to $J$. If it does, it appears in the lifted restriction exactly when it belongs to $S$, and it cannot belong to $S\setminus J$. If it does not, it cannot appear in the lifted restriction, and it belongs to $S\setminus J$ exactly when it belongs to $S$. In either case, membership in the union is equivalent to membership in $S$.
