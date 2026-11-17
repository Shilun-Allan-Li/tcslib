<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.onePointFlippedParity_ne_fullParity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-point flip differs from parity

**Claim.** For every $k\ge 0$, the function obtained by negating full parity at the all-ones input is not equal to full parity.

**Proof.** Suppose the two functions were equal. Evaluating them at the all-ones input preserves that equality. There the one-point-flipped function takes the negative of parity, whereas full parity takes parity. Since every coordinate of this input is $1$, full parity equals $1$, so the asserted equality would say $-1=1$, a contradiction.
