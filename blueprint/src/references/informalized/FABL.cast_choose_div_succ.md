<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.cast_choose_div_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial quotient identity

**Claim.** For natural numbers $n$ and $k$, $(\binom{n}{k})/(k+1)=\binom{n+1}{k+1}/(n+1)$.

**Proof.** The binomial recurrence in product form states $(n+1)\binom{n}{k}=(k+1)\binom{n+1}{k+1}$. Regard this as an equality of real numbers and divide by the positive product $(k+1)(n+1)$. The resulting equality is the claimed quotient identity.
