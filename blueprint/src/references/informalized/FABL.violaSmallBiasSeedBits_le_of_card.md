<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaSeedLength.lean :: FABL.violaSmallBiasSeedBits_le_of_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seed Length from Generator Size

**Claim.** Under the stated positivity and cardinality assumptions, the seed length $2d\ell$ is at most $d\bigl(4+2(\log_2 n+2^{d-1}\log_2(9/\varepsilon))\bigr)$.

**Proof.** The generator multiset has cardinality $(2^\ell)^2$. The assumed upper bound on this cardinality therefore gives $(2^\ell)^2\leq16(n/B(\varepsilon,d))^2$. Both sides are positive, and logarithm to base $2>1$ preserves the inequality. The logarithm of the left side is $2\ell$. The logarithm of the right side is $4+2(\log_2 n+2^{d-1}\log_2(9/\varepsilon))$, using the definition of $B$ and the logarithm laws; this is precisely the support-envelope logarithm identity (\texttt{logb\_smallBiasSupportEnvelope\_eq}). Multiplying this inequality by $d\geq0$ preserves its direction. Since the seed length is $2d\ell$, the resulting bound is the claimed one.

**Key facts.** `FABL.smallBiasGeneratorMultiset_card`, `FABL.logb_smallBiasSupportEnvelope_eq`.
