<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.onePointFlippedParity_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real form of the one-point flip

**Claim.** For every $k\ge 0$, the real-valued form of the one-point-flipped full parity equals real-valued full parity minus $2$ at the all-ones input, and equals real-valued full parity elsewhere.

**Proof.** Fix an input and split into whether it is the all-ones input. At that input, all coordinates are $1$, so full parity is $1$ and the flipped value is $-1$; after viewing signs as real numbers, this is exactly the parity value minus $2$. At any other input, the definition leaves parity unchanged, and the correction term is zero. Thus the two functions agree at every input.
