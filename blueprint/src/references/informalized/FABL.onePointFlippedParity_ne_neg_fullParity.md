<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.onePointFlippedParity_ne_neg_fullParity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-point flip differs from negative parity

**Claim.** For every $k\ge 0$, the function obtained by negating full parity at the all-ones input is not equal to negative full parity.

**Proof.** Choose an input whose coordinate $0$ is $-1$ and whose other coordinates are $1$. This input is not the all-ones input, so the flipped function agrees with full parity there. If it were everywhere equal to negative full parity, evaluating at this input would give $P=-P$, where $P$ is the value of full parity. A product of signs is itself a sign, hence $P$ is either $1$ or $-1$, and neither value equals its own negative. This is a contradiction.
