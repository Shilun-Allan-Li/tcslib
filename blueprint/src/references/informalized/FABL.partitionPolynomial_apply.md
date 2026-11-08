<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.partitionPolynomial_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Partition Polynomial

**Claim.** For any $m$-dimensional sign vector $w$, the partition polynomial associated with $p,z,\pi$ evaluates to $p((z_iw_{\pi(i)})_{i=1}^n)$.

**Proof.** Expand the partition polynomial as a sum over frequencies $T$ in the smaller cube, with each coefficient itself summing over those original frequencies $S$ whose identified frequency is $T$. Distributing each monomial factor through that inner sum and then regrouping by $S$ yields a single sum over all original frequencies, with the factor $\operatorname{monomial}(\operatorname{identifiedFrequency}(\pi,S),w)$. The monomial identity for the partition input says that this factor times $\operatorname{monomial}(S,z)$ equals $\operatorname{monomial}(S,(z_iw_{\pi(i)})_i)$ (`FABL.monomial_partitionInput`). Thus the sum is the Fourier expansion of $p$ evaluated at that input, which equals $p((z_iw_{\pi(i)})_i)$ (`FABL.fourier_expansion`).

**Key facts.** `FABL.monomial_partitionInput`, `FABL.fourier_expansion`.
