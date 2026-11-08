<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/RandomSmallBias.lean :: FABL.measure_randomSmallBiasDensity_not_isBiased_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random empirical density is small biased

**Claim.** For positive \(n\) and \(0<\varepsilon<1\), the probability that the empirical density formed from the prescribed number of independent uniform cube samples has a nonzero Fourier coefficient with absolute value greater than \(\varepsilon\) is at most \(2^{-n}\).

**Proof.** First identify the event that this empirical density is not \(\varepsilon\)-biased with the previously defined failure event for the sample sequence. The equivalence between density bias and sample small-bias (\(\texttt{randomSmallBiasDensity_isBiased_iff}\)) gives this identification; the sample count is positive under \(n>0\) and \(\varepsilon>0\) (\(\texttt{randomSmallBiasSampleCount_pos}\)). The probability bound for the sample failure event is at most \(2^{-n}\) (\(\texttt{measure_randomSmallBiasSample_not_isBiased_le}\)), and thus gives the claimed bound for the density event.

**Key facts.** `FABL.randomSmallBiasDensity_isBiased_iff`, `FABL.randomSmallBiasSampleCount_pos`, `FABL.measure_randomSmallBiasSample_not_isBiased_le`.
