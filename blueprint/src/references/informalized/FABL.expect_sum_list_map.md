<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.expect_sum_list_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation commutes with a list sum

**Claim.** For a finite nonempty set $\Omega$, expectation of the list sum of functions equals the list sum of their expectations.

**Proof.** Induct on the list. For the empty list, both sides are zero. For a list beginning with $a$, its pointwise sum is $f(a)$ plus the sum over the remaining list. Linearity of expectation separates these terms, and the induction hypothesis identifies the expectation of the remaining sum with the sum of its expectations. This is precisely the claimed equality.
