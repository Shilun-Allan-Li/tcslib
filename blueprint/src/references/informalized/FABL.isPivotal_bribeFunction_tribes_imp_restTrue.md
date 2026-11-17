<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.isPivotal_bribeFunction_tribes_imp_restTrue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivotality forces the rest of the tribe block to be negative

**Claim.** If $i$ lies outside the bribed set and the bribed tribes function is pivotal at $i$, then every other coordinate in $i$’s block has value $-1$ in the original input.

**Proof.** Because $i\notin J$, bribing the input and then flipping coordinate $i$ gives the same point as first bribing the input and then flipping coordinate $i$ (`FABL.bribeInput_flipCoordinate_of_not_mem`). Thus pivotality of the bribed function implies pivotality of the ordinary tribes function at the bribed input. The characterization of pivotality for tribes says that every other coordinate in the same block must be $-1$ there (`FABL.isPivotal_tribes_iff`). Now fix any such other coordinate $o$, and let $j$ be its corresponding coordinate in the full input. The coordinate correspondence for the product indexing ensures that $j\ne i$ (`FABL.finProdFinEquiv_tribesCoord`). The tribes characterization gives that the bribed input has value $-1$ at $j$. If $j$ belonged to $J$, its bribed value would instead be $+1$, a contradiction. Therefore $j\notin J$, and its bribed value equals its original value $x_j$. Hence $x_j=-1$, as required.

**Key facts.** `FABL.bribeInput_flipCoordinate_of_not_mem`, `FABL.isPivotal_tribes_iff`, `FABL.finProdFinEquiv_tribesCoord`.
