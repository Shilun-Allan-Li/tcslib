<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.measure_prescribedFourierOffCenterSum_abs_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Off-center Fourier sum tail bound

**Claim.** For a fixed cube point \(x\), under the stated hypotheses on \(\mathcal F\) and \(\varepsilon\), the probability that the absolute prescribed off-center Fourier sum at \(x\) is at least \(\varepsilon\) is at most \(4^{-n}\).

**Proof.** First handle \(n=0\): the desired bound is \(1\), so it follows because a probability is at most one. Now suppose \(n>0\). Write the off-center sum as \(\sum_a w(a)f(a)\), where \(w(x)=0\) and \(w(a)\) is the prescribed Fourier kernel for \(a\ne x\); this is exactly the weighted-sum identity (\(\texttt{prescribedFourierOffCenterSum_eq_weightedSum}\)). The squared weights sum to \(|\{-1,1\}^n|/|\mathcal F|-1\) (\(\texttt{sum_sq_prescribedFourierOffCenterWeight}\)). The size assumption and the variance estimate bound this sum by \(\varepsilon^2/(5n)\) (\(\texttt{prescribedFourierOffCenterVariance_le}\)). If the sum of squared weights is zero, every weight is zero, so the off-center sum vanishes and the event is empty because \(\varepsilon>0\). Otherwise, apply the weighted Boolean-sum tail estimate: the event has probability at most \(2\exp(-\varepsilon^2/(2\sum_a w(a)^2))\) (\(\texttt{measure_abs_weightedBooleanSum_ge_le}\)). The variance bound makes the exponent at most \(-5n/2\). Finally, \(2\exp(-5n/2)\le 4^{-n}\) for positive \(n\) (\(\texttt{two_mul_exp_neg_five_halves_mul_le_four_pow_inv}\)).

**Key facts.** `FABL.prescribedFourierOffCenterSum_eq_weightedSum`, `FABL.sum_sq_prescribedFourierOffCenterWeight`, `FABL.prescribedFourierOffCenterVariance_le`, `FABL.measure_abs_weightedBooleanSum_ge_le`, `FABL.two_mul_exp_neg_five_halves_mul_le_four_pow_inv`.
