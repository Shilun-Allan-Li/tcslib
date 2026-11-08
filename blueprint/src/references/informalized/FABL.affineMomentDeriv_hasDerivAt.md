<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.affineMomentDeriv_hasDerivAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Affine Moment Derivative

**Claim.** Where every base $1+ctX(x)$ is positive, the derivative of the affine moment derivative at $t$ is the second affine moment derivative at $t$.

**Proof.** Write the finite average as a sum divided by the cardinality of the finite sample space. Differentiate the sum term by term, which is valid because it is finite. For a fixed $x$, the base $1+csX(x)$ is affine in $s$ with derivative $cX(x)$. Positivity at $s=t$ permits the real-power derivative rule for the exponent $r-1$; multiplying by the constant factor $rcX(x)$ gives derivative $r(r-1)c^2X(x)^2(1+ctX(x))^{r-2}$. Summing these derivatives and dividing by the cardinality gives exactly the stated second affine moment derivative.
