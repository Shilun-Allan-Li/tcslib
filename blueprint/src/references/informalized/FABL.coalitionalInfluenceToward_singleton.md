<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluenceToward_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Coalitional Influence

**Claim.** The influence of the singleton coalition containing coordinate $i$ toward $b$ equals half the probability that flipping coordinate $i$ changes the function's value.

**Proof.** For each input, the singleton coalition can attain $b$ exactly when at least one of the two values obtained by setting coordinate $i$ to $+1$ or $-1$ equals $b$ (`coalitionCanAttain_singleton_iff`). Write $I_+$ and $I_-$ for the indicators that these two values equal $b$. The original probability of output $b$ equals the average of $I_+$ and $I_-$ over the cube: averaging first over the two choices of coordinate $i$ does not change the uniform mean (`mean_coordinateExpectation`), and the two-point average is given by `coordinateExpectation_apply`. Pointwise, since both function values and $b$ are signs, the indicator of the event that at least one equals $b$ is $(I_+ + I_- + P)/2$, where $P$ indicates that the two values differ. Indeed, if both equal $b$, the expression is $1$; if exactly one equals $b$, it is also $1$; and if neither equals $b$, the two values coincide and it is $0$. The pivotal indicator $P$ is precisely the event that the two coordinate-fixed values differ (`isPivotal_iff_setCoordinate_ne`). Taking uniform means, the baseline terms cancel, leaving half the mean of $P$, which is half the Boolean influence.

**Key facts.** `FABL.coalitionCanAttain_singleton_iff`, `FABL.mean_coordinateExpectation`, `FABL.coordinateExpectation_apply`, `FABL.isPivotal_iff_setCoordinate_ne`.
