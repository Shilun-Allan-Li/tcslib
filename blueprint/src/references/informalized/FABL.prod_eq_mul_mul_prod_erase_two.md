<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.prod_eq_mul_mul_prod_erase_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factoring Two Terms from a Product

**Claim.** For distinct elements $a,b$ of a finite set $P$, its product of values factors as $F(a)F(b)$ times the product over the elements other than $a$ and $b$.

**Proof.** Factor out the term indexed by $a$ from the product over all of $P$. Then factor out the term indexed by $b$ from the remaining product; distinctness ensures that $b$ is still present after removing $a$. The remaining indices are exactly those in $P\setminus\{a,b\}$. Commutativity and associativity of multiplication put the factors in the stated order.
