<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.signEncode_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding of a Finite Sum

**Claim.** For a finite set $S$ and a family $a_i\in\mathbb{F}_2$, the sign encoding of their sum is the product of their sign encodings.

**Proof.** Induct on the finite set. For the empty set, both sides are $1$. For the step, write the enlarged set as $\{i\}\cup S$, where $i\notin S$. The sum becomes $a_i+\sum_{j\in S}a_j$, and its sign encoding is the product of the encodings of these two summands by the addition law for sign encoding (\texttt{FABL.signEncode_add}). The induction hypothesis identifies the second factor with the product over $S$, and adjoining the factor for $i$ gives the stated product.

**Key facts.** `FABL.signEncode_add`.
