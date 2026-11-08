<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.affineMomentDeriv2_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Affine Moment Derivative at Zero

**Claim.** At $t=0$, the average of $r(r-1)c^2X(x)^2(1+ctX(x))^{r-2}$ equals $r(r-1)c^2$ times the average of $X(x)^2$.

**Proof.** At zero, each factor $1+ctX(x)$ equals $1$, and its real power is therefore $1$. The summand reduces to $r(r-1)c^2X(x)^2$. Express both finite averages as sums divided by the cardinality of the nonempty set. Pull the constant factor $r(r-1)c^2$ outside the sum; the resulting expressions agree.
