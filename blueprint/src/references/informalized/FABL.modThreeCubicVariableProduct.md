<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicVariableProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of cubic factors

**Claim.** For a subset of coordinates, the product of the factors $(-\sqrt{3}\,x_i)\,\mathrm{i}$ equals $(-\sqrt{3})^{|S|}(\prod_{i\in S}x_i)\,\mathrm{i}^{|S|}$.

**Proof.** Proceed by induction on the finite set $S$. For $S=\varnothing$, both products are empty products, hence equal to $1$. For the inductive step, write $S=\{i\}\cup T$ with $i\notin T$. The product over $S$ is the factor at $i$ multiplied by the product over $T$. By the induction hypothesis, the latter is $(-\sqrt{3})^{|T|}(\prod_{j\in T}x_j)\,\mathrm{i}^{|T|}$. Meanwhile, adjoining $i$ multiplies the monomial by $x_i$ and increases the cardinality by one. Substituting these expressions, the two sides agree by associativity and commutativity of multiplication and the laws of integer powers.
