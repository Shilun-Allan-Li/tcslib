<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.freeWithin_fixCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Coordinates After Fixing One Coordinate

**Claim.** If every coordinate free under $\rho$ belongs to $A$, then after fixing coordinate $i$ according to $s$, every coordinate that remains free belongs to $A\setminus\{i\}$.

**Proof.** Take a coordinate $j$ that remains free. If $j=i$, its state is the state determined by $s$, which is not free; this contradicts the choice of $j$. Hence $j\ne i$. Fixing coordinate $i$ leaves the state at $j$ unchanged, so $j$ was already free under $\rho$ and therefore belongs to $A$. Together, $j\ne i$ and $j\in A$ say that $j$ belongs to $A\setminus\{i\}$.

**Key facts.** `FABL.CoordRestriction.fixedState_ne_free`, `FABL.CoordRestriction.fixCoordinate_apply_of_ne`.
