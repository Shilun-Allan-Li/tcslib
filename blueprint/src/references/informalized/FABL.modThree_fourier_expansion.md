<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThree_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier expansion

**Claim.** The indicator that the integer coordinate sum is divisible by $3$ equals $\frac13+\frac23(-\frac12)^n\sum_{S:|S|\text{ even}}(-1)^{(|S|\bmod 4)/2}(\sqrt3)^{|S|}\prod_{i\in S}x_i$.

**Proof.** Use the cubic root filter formula to express the indicator as $1/3+2/3$ times the real part of the product of the coordinate factors. The real-part computation for that product gives $(-1/2)^n$ times the sum over even-cardinality subsets, with each summand weighted by $(-1)^{(|S|\bmod 4)/2}(\sqrt3)^{|S|}$ and multiplied by the coordinate monomial (\texttt{modThreeCubicProduct_re}). Substituting this identity into the root-filter formula and collecting the scalar factors gives the claimed expansion.

**Key facts.** `FABL.modThree_eq_cubicRootFilter`, `FABL.modThreeCubicProduct_re`.
