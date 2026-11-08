<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.binaryFourierCoeff_realSignEncodedFunction_eq_one_sub_two_relativeHammingDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient and relative Hamming distance

**Claim.** For a binary-valued function $f$ and a coordinate set $S$, the Fourier coefficient of its real sign encoding equals $1-2$ times the relative Hamming distance from $f$ to the coordinate sum associated with $S$.

**Proof.** Uniform averaging turns the relative Hamming distance into the expected indicator of the event $f(x)\ne\sum_{i\in S}x_i$. At each point $x$, the product of the sign encodings of these two binary values is $1$ when they agree and $-1$ when they differ. Equivalently, it is $1-2$ times the indicator that they differ. Averaging this pointwise identity gives one minus twice the probability of disagreement, which is the claimed relative Hamming distance.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.signValue_signEncode_eq_binarySign`, `FABL.signEncoded_mul_eq_one_sub_two_indicator_ne`.
