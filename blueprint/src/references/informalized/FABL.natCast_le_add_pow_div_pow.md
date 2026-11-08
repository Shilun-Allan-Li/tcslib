<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.natCast_le_add_pow_div_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound by a Power Quotient

**Claim.** For natural numbers $d,q$, considered as real numbers, $d\le q+2^d/2^q$.

**Proof.** If $d\le q$, the quotient of powers is nonnegative, so the inequality follows at once. Otherwise write $d=q+r$, where $r=d-q$. The elementary bound $r\le 2^r$ follows from the fact that every natural number is at most the corresponding power of $2$. Also, $2^d/2^q=2^r$, by the exponent decomposition $d=q+r$. Thus $d=q+r\le q+2^r=q+2^d/2^q$.
