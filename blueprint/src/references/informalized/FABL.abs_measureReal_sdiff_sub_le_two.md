<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BerryEsseenIntervals.lean :: FABL.abs_measureReal_sdiff_sub_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measure Difference on a Set Difference

**Claim.** If $t\subseteq s$ and $t$ is measurable, bounds of $B$ on the absolute measure differences of $s$ and $t$ imply a bound of $2B$ on the absolute measure difference of $s\setminus t$.

**Proof.** For each probability measure, the measure of $s\setminus t$ is the measure of $s$ minus the measure of $t$, by the measure formula for a measurable subset. Thus the difference between the two measures of $s\setminus t$ is the difference of their measure differences on $s$ and on $t$. The triangle inequality bounds its absolute value by the sum of the two given bounds, namely $B+B=2B$.
