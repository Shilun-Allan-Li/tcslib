<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.monomial_binaryCubeSignEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characters under sign encoding

**Claim.** For every coordinate set $S$ and bit assignment $x$, the sign monomial on $S$ after encoding the bits equals the character $\chi_S(x)$.

**Proof.** Proceed by induction on the finite set $S$. For the empty set, both expressions are $1$. If $S$ is obtained by adjoining a coordinate $i$ not already in $S$, the encoded sign product gains the factor corresponding to the bit $x_i$. The sign of the encoded bit is precisely the binary character evaluated at that bit (by `signValue_signEncode_eq_binarySign`). The induction hypothesis identifies the remaining product with the character of the sum of the bits over $S$. Finally, the character of a sum is the product of the characters of its summands, so adjoining $i$ gives exactly the character for the sum over $S\cup\{i\}$.

**Key facts.** `FABL.binaryCubeSignEquiv_apply`, `FABL.signValue_signEncode_eq_binarySign`.
