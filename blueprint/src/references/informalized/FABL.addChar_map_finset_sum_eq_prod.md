<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.addChar_map_finset_sum_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additive Characters and Finite Sums

**Claim.** For an additive commutative monoid $A$, a commutative monoid $M$, an additive character $\chi:A\to M$, a finite set $s$, and a family $(a_i)$ in $A$, the character of the finite sum is the product of the characters: $\chi(\sum_{i\in s}a_i)=\prod_{i\in s}\chi(a_i)$.

**Proof.** Induct on the finite set. For the empty set, the sum is zero and the product is the identity, so the equality follows from an additive character preserving zero. For the inductive step, write the set as a new element $i$ adjoined to $s$. The sum splits as $a_i+\sum_{j\in s}a_j$, and the character sends this sum to the product of the two character values. By the induction hypothesis, the second value is the product over $s$; adjoining the factor at $i$ gives the product over the enlarged set.
