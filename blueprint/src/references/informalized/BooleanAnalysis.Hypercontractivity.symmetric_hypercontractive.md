<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Symmetric.lean :: BooleanAnalysis.Hypercontractivity.symmetric_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric hypercontractivity

**Claim.** For a symmetric random variable with unit $L^2$ norm and $L^q$ norm $C$, where $q>2$ and $C>0$, the stated radius $1/(C\sqrt{q-1})$ gives the affine $L^q$ versus $L^2$ norm inequality required for hypercontractivity.

**Proof.** Let $s=\sqrt{q-1}$ and write $A(a,b)=a+bX$. Symmetry makes the $q$th moments of $A(a,b)$ and $A(a,-b)$ equal. Averaging these moments cancels all odd powers of $X$; the two-point power inequality (\texttt{BooleanAnalysis.Hypercontractivity.two\_point\_rpow\_le}) then bounds the average pointwise by the $(q/2)$th power of $a^2+(q-1)b^2X^2$. Minkowski's inequality for the resulting $L^{q/2}$ norm, together with the identity converting the norm of $X^2$ to the square of the $L^q$ norm (\texttt{BooleanAnalysis.Hypercontractivity.rvLpNorm\_rpow}), yields $\|A(a,b)\|_q^2\le a^2+(q-1)b^2C^2$. The unit second norm and zero mean give $\|A(a,b)\|_2^2=a^2+b^2$ by the affine second-moment identity (\texttt{BooleanAnalysis.Hypercontractivity.rvLpNorm\_affine\_sq}). Now take $\rho=1/(Cs)$. Since norm monotonicity gives $C\ge1$ and $s>1$, we have $0\le\rho<1$. Moreover, $(q-1)\rho^2C^2=1$. Applying the preceding $q$-norm bound with $b$ replaced by $\rho b$ gives $\|A(a,\rho b)\|_q^2\le a^2+b^2=\|A(a,b)\|_2^2$, hence the required norm inequality for every $a,b$. Membership and exponent conditions are supplied by the hypotheses and $q>2$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.two_point_rpow_le`, `BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow`, `BooleanAnalysis.Hypercontractivity.rvLpNorm_affine_sq`.
