<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.dnfSwitchingDepth_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Switching Depth

**Claim.** If $0<\varepsilon\le1$, then $\lceil\log_2(3/\varepsilon)\rceil$ is positive.

**Proof.** The assumptions imply $3/\varepsilon\ge3>1$. Since the logarithm to base $2>1$ is positive on arguments greater than $1$, $\log_2(3/\varepsilon)>0$. The ceiling of a positive real number is a positive natural number, as required.
