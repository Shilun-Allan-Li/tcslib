<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.measure_positiveCoordinateCount_gt_typicalCutoff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper tail of positive coordinates

**Claim.** For positive \(n\), the probability that a uniformly chosen point of the sign cube has more positive coordinates than the stated floor cutoff is at most \(1/(24n)\).

**Proof.** Set \(\delta=\sqrt{2\log(48n)/n}\), which is nonnegative since \(n>0\). A uniform point of the sign cube is a sample of \(n\) independent signs. Each sign has mean zero (\(\texttt{expect_signValue_prescribedFourierSupport}\)) and lies in \([-1,1]\) (\(\texttt{signValue_eq_neg_one_or_one}\)). The empirical-mean concentration estimate therefore bounds the probability that the absolute empirical mean is at least \(\delta\) by \(2\exp(-n\delta^2/2)\) (\(\texttt{measure_finiteUniformEmpiricalMean_sub_expect_ge_le}\)). If the positive-coordinate count exceeds the floor cutoff, it exceeds the real number \(n/2+(n/2)\delta\). The sum of the signs is twice the positive-coordinate count minus \(n\) (\(\texttt{sum_signValue_eq_two_mul_positiveCoordinateCount_sub}\)); hence the empirical mean is greater than \(\delta\), so this tail event is contained in the concentration event. Substituting the definition of \(\delta\) gives \(2\exp(-\log(48n))=1/(24n)\), as required.

**Key facts.** `FABL.expect_signValue_prescribedFourierSupport`, `FABL.measure_finiteUniformEmpiricalMean_sub_expect_ge_le`, `FABL.signValue_eq_neg_one_or_one`, `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`.
