<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.signEncode_coordinateSum_local -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign of a Coordinate Sum

**Claim.** For a finite set of coordinates, the sign encoding of their sum in $\mathbb{F}_2$ is the product of the sign encodings of the individual coordinates.

**Proof.** Proceed by induction on the finite set $S$. If $S$ is empty, the sum is $0$ and the product is $1$, so the claim follows from the empty-sum and empty-product identities. For the induction step, write $S'=\{i\}\cup S$ with $i\notin S$. The sum over $S'$ is $x_i+\sum_{j\in S}x_j$, while the product over $S'$ is the factor for $i$ times the product over $S$. The sign encoding converts addition in $\mathbb{F}_2$ into multiplication of signs (\texttt{FABL.signEncode_add}); applying this and the induction hypothesis gives the desired product.

**Key facts.** `FABL.signEncode_add`.
