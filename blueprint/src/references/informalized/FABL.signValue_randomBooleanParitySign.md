<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.signValue_randomBooleanParitySign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Boolean Parity Sign

**Claim.** For a subset $S\subseteq\{1,\ldots,n\}$ and $x\in\{-1,1\}^n$, the real value of the sign obtained by multiplying the coordinates $x_i$ for $i\in S$ equals the monomial $\prod_{i\in S}x_i$.

**Proof.** The parity sign is the product of the selected coordinates, while the monomial is the product of their real values. Taking the real value of a product of signs gives the product of their real values, so the two products agree. This also covers the empty subset: both products are $1$.
