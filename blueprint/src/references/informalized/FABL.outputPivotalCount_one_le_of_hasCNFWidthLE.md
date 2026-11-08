<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.outputPivotalCount_one_le_of_hasCNFWidthLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivotal count bound from CNF width

**Claim.** If $f$ has a CNF representation of width at most $w$, then at every cube point the number of coordinates where $f$ equals $1$ and is pivotal is at most $w$.

**Proof.** Choose a CNF formula $\psi$ of width at most $w$ representing $f$. Switch its conjunctions and disjunctions to obtain a DNF formula $\phi$; switching preserves width, so $\phi$ also has width at most $w$. The switched formula computes the Boolean dual of $f$ (switchAndOr_toBooleanFunction). Negating every coordinate of the input identifies coordinates where $f(x)=1$ and $f$ is pivotal with coordinates where the dual formula is $-1$ and pivotal (isNegOnePivotal_booleanDual_negate_iff). Therefore the desired count equals the number of $-1$-pivotal coordinates for $\phi$ at the negated input. The DNF pivotal-count bound (card_negOnePivotal_le_width) bounds this by the width of $\phi$, hence by $w$.

**Key facts.** `FABL.CNFFormula.switchAndOr_toBooleanFunction`, `FABL.isNegOnePivotal_booleanDual_negate_iff`, `FABL.card_negOnePivotal_le_width`.
