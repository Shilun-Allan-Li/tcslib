<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.pmfExpectation_mem_Icc_zero_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for expectations in the unit interval

**Claim.** If $0\le g(x)\le 1$ for every $x$, then the expectation of $g$ under $p$ lies in $[0,1]$.

**Proof.** Using the finite-sum definition of expectation, each summand $(p(x)).\mathrm{toReal}\,g(x)$ is nonnegative, since both factors are nonnegative. Thus the expectation is nonnegative. For the upper bound, compare each summand with $(p(x)).\mathrm{toReal}\cdot 1$; the pointwise assumption $g(x)\le 1$ and nonnegativity of the weight justify this comparison. Summing gives an expectation at most that of the constant function $1$, which equals $1$ (`FABL.pmfExpectation_const_one`).

**Key facts.** `FABL.pmfExpectation_const_one`.
