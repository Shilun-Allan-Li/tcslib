<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.correlationImmuneAndExample_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Formula for the Parity-Based Function

**Claim.** For every positive integer $m$, the real-valued version of the function obtained by taking the AND of the parities on the first and last $2m$ coordinates is, at each input $x\in\{-1,1\}^{3m}$, equal to one half of $1$ plus the monomial on the first coordinate set plus the monomial on the last coordinate set minus the monomial on their symmetric difference.

**Proof.** Fix an input $x$. The real-valued two-input AND identity expresses the output on signs $a,b$ as $(1+a+b-ab)/2$ (`andFunction_two_toReal`). Apply it to the two parity outputs. The real value of each parity is its corresponding monomial, by the parity-to-monomial identity (`parityFunction_toReal`). Finally, the product of the two monomials is the monomial indexed by the symmetric difference of their coordinate sets (`monomial_mul_monomial`). Substitution gives the claimed formula at every input.

**Key facts.** `FABL.andFunction_two_toReal`, `FABL.parityFunction_toReal`, `FABL.monomial_mul_monomial`.
