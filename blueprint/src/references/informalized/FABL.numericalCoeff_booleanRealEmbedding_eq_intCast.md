<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.numericalCoeff_booleanRealEmbedding_eq_intCast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Coefficients and the Möbius Sum

**Claim.** For a Boolean-valued function, its numerical coefficient at $S$ equals the integer alternating sum over subsets of $S$, cast to the reals.

**Proof.** The coefficient is given by the Möbius sum over $T\subseteq S$ (`FABL.numericalCoeff_eq_mobius_sum`). Substitute the indicator value of the Boolean real embedding at each point $\mathbf 1_T$. Casting the integer sum to the reals distributes over the finite sum and each product. For each $T$, if $f(\mathbf 1_T)=1$, the indicator is $1$; otherwise it is $0$. Thus the summand is exactly the real cast of the corresponding integer alternating-sum summand, proving the equality.

**Key facts.** `FABL.numericalCoeff_eq_mobius_sum`.
