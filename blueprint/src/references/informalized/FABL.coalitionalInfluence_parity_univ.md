<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluence_parity_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Has Maximal Coalitional Influence

**Claim.** If $J$ is nonempty, then parity on all $n$ coordinates has coalitional influence $1$ with respect to $J$.

**Proof.** Choose a coordinate $i\in J$. For any input $x$, parity already attains its current sign at $x$. Flipping coordinate $i$ leaves every coordinate outside $J$ unchanged, since $i\in J$ (`FABL.setCoordinate_apply_of_ne`). Parity on the full coordinate set changes sign under this flip (`FABL.parityFunction_univ_flipCoordinate`), so the modified input attains the opposite sign. Hence both signs are attainable from every input while changing only coordinates in $J$. The event defining coalitional influence therefore holds everywhere, and its uniform probability is one.

**Key facts.** `FABL.setCoordinate_apply_of_ne`, `FABL.parityFunction_univ_flipCoordinate`.
