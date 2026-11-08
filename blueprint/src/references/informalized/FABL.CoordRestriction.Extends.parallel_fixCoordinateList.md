<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.Extends.parallel_fixCoordinateList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parallel fixing preserves extension

**Claim.** If fixing the listed coordinates of ρ according to $x$ gives a restriction extended by τ, then fixing those coordinates in both restrictions according to $y$ preserves the extension relation.

**Proof.** Fix a coordinate $i$ at which the restriction obtained by fixing ρ according to $y$ is not free. Split according to whether $i$ belongs to the coordinate list. If it does, the no-repetition hypothesis ensures that fixing a list sets that coordinate to the fixed state prescribed by its sign, independently of the starting restriction and of $x$ or $y$. Thus both restrictions formed using $y$ agree there. If $i$ is absent from the list, fixing the list leaves its state unchanged. The assumed nonfree state of the restriction formed from ρ using $y$ therefore says that $\rho(i)$ is not free. The corresponding state after fixing ρ according to $x$ is also $\rho(i)$, so the assumed extension from that restriction to τ forces $\tau(i)=\rho(i)$. Fixing the list in τ according to $y$ leaves this absent coordinate unchanged as well. Hence the two restrictions formed using $y$ agree at $i$, as required.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_apply_of_mem`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
