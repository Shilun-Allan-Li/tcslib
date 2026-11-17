<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.matrixRowSpanDensity_isKWiseIndependent_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row-span density and column sums

**Claim.** Let $H$ be an $m\times n$ matrix over $\mathbb F_2$, and let $A\leq\mathbb F_2^n$ be its row span. Then the associated row-span density is $k$-wise independent exactly when every sum of between one and $k$ columns of $H$ is nonzero in $\mathbb F_2^m$.

**Proof.** First translate the Fourier-regularity condition on the sign cube into its vector form: it says that every nonzero $\gamma\in\mathbb F_2^n$ whose support has size at most $k$ has vector Fourier coefficient of absolute value at most zero (\texttt{FABL.isLowDegreeFourierRegular\_binaryFunctionOnSignCube\_iff}). The support of a vector is nonempty exactly when the vector is nonzero (\texttt{FABL.f₂Support\_nonempty\_iff}). The coefficient of the row-span density is $1$ when $H\gamma=0$ and $0$ otherwise (\texttt{FABL.vectorFourierCoeff\_matrixRowSpanDensity}).

Suppose first that the Fourier-regularity condition holds. Take a nonempty set $S$ of at most $k$ column indices and suppose its column sum were zero. Let $\gamma$ be the indicator vector of $S$. Its support is $S$, so it is nonzero and has support size at most $k$. Its matrix-vector product $H\gamma$ is precisely the sum of the columns indexed by $S$, hence is zero. The coefficient formula then gives coefficient $1$, contradicting the required bound by zero. Thus every such column sum is nonzero.

Conversely, suppose every nonempty column set of size at most $k$ has nonzero sum. Take any nonzero $\gamma$ with support size at most $k$. Its support is nonempty, and its matrix-vector product is the sum of the columns indexed by that support, so the hypothesis makes $H\gamma\ne0$. The coefficient formula therefore gives coefficient zero, whose absolute value is at most zero. This proves the vector Fourier-regularity condition, and hence the claimed equivalence.

**Key facts.** `FABL.isLowDegreeFourierRegular_binaryFunctionOnSignCube_iff`, `FABL.f₂Support_nonempty_iff`, `FABL.vectorFourierCoeff_matrixRowSpanDensity`.
