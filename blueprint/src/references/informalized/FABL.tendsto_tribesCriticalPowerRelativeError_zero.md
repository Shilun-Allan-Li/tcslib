<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_tribesCriticalPowerRelativeError_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Power Relative Error Vanishes

**Claim.** The relative error $2^w\log(D_w)/D_w-1$, where $D_w$ is the tribes critical dimension, tends to zero as $w\to\infty$.

**Proof.** The error is little-$o$ of the constant function $1$ (\texttt{tribesCriticalPowerRelativeError\_isLittleO\_one}). For a function tending along the natural numbers to a nonzero constant, being little-$o$ of that constant is equivalent to tending to zero. Applying this characterization gives the asserted limit.

**Key facts.** `FABL.tribesCriticalPowerRelativeError_isLittleO_one`.
