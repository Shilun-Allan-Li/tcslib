<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.discreteDerivative_majority_odd_last_eq_middleLayerIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Derivative and the Middle Layer

**Claim.** For a sign vector $x$ of length $2m$, the discrete derivative of majority in the last coordinate, evaluated at $x$ with a final $1$, equals the indicator that $x$ has exactly $m$ positive coordinates.

**Proof.** Let $c$ be the number of positive coordinates of $x$. The sum of the signs of its coordinates is $2c-2m$ (\texttt{FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub}). Appending $1$ or $-1$ changes this sum to $2c-2m+1$ or $2c-2m-1$, respectively. The derivative is the difference between the two majority values at these appended vectors, divided by $2$; this is the derivative evaluation formula (\texttt{FABL.discreteDerivative_apply}). Majority is determined by whether the corresponding sign sum is nonnegative, as expressed by the threshold-sign evaluation fact (\texttt{FABL.signValue_thresholdSign}). If $c=m$, the two sums are $1$ and $-1$, so the two outputs are $1$ and $-1$, and the derivative is $1$, equal to the middle-layer indicator. If $c<m$, integrality gives $c+1\le m$, so both sums are negative and both outputs are $-1$; the derivative is $0$. If $c>m$, integrality gives $m+1\le c$, so both sums are nonnegative and both outputs are $1$; again the derivative is $0$. In both remaining cases the middle-layer indicator is also zero.

**Key facts.** `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`, `FABL.discreteDerivative_apply`, `FABL.signValue_thresholdSign`.
