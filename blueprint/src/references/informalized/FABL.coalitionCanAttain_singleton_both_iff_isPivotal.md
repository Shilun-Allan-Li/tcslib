<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionCanAttain_singleton_both_iff_isPivotal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Coalition and Pivotality

**Claim.** A coalition consisting of coordinate $i$ can attain both output signs from $x$ if and only if flipping coordinate $i$ changes the value of $f$ at $x$.

**Proof.** The singleton-coalition criterion says that attaining a specified sign is equivalent to that sign appearing among the two values $f(x^{i\gets 1})$ and $f(x^{i\gets -1})$ (`coalitionCanAttain_singleton_iff`). Thus attaining both signs is equivalent to these two values being different: each is a sign, so if they differ they are precisely $1$ and $-1$, and if they are equal they cannot include both. The characterization of pivotality by inequality of these two coordinate-fixed values (`isPivotal_iff_setCoordinate_ne`) identifies this condition with pivotality.

**Key facts.** `FABL.coalitionCanAttain_singleton_iff`, `FABL.isPivotal_iff_setCoordinate_ne`.
