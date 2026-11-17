<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.prod_paddedParityInput_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of padded parity inputs

**Claim.** When a sign vector of length $n$ is extended to length $m$ by appending signs equal to $1$, the product of all $m$ coordinates equals the product of the original $n$ coordinates.

**Proof.** Separate the length-$m$ indices according to whether they are below $n$. The coordinates at those indices are exactly the original entries, while every remaining factor is $1$, so they do not affect the product. The indices below $n$ are in bijection with the length-$n$ indices via the inclusion of the initial segment (the equivalence `Fin.castLEquiv hnm`), and corresponding factors agree. Thus the two products are equal.
