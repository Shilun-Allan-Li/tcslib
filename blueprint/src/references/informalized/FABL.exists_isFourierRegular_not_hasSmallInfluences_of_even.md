<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.exists_isFourierRegular_not_hasSmallInfluences_of_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier regularity with a large influence

**Claim.** For every positive even $n$, there is a Boolean function whose nonempty Fourier coefficients have absolute value at most $2^{-n/2}$, but whose influences cannot all be at most any $\varepsilon<1/2$.

**Proof.** Write $n=2m$; positivity of $n$ gives $m>0$. Take the inner-product-mod-two Boolean function on $2m$ coordinates. Its Fourier regularity bound is $2^{-m}$, by `isFourierRegular_innerProductModTwoBoolean`, and $2^{-m}=2^{-n/2}$. If this function had all influences at most some $\varepsilon<1/2$, the equivalence between small influences and coordinatewise influence bounds (`hasSmallInfluences_iff`) would give that bound in particular for the first coordinate. But every coordinate influence of this function equals $1/2$ (`influence_innerProductModTwoBoolean_eq_half`), contradicting $\varepsilon<1/2$.

**Key facts.** `FABL.isFourierRegular_innerProductModTwoBoolean`, `FABL.hasSmallInfluences_iff`, `FABL.influence_innerProductModTwoBoolean_eq_half`.
