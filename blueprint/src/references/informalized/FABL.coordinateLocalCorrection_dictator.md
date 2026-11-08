<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.coordinateLocalCorrection_dictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local correction recovers a dictator

**Claim.** For any Boolean string $w$, coordinate $j$, and vector $y$ over the Boolean cube, applying local correction to the dictator that reads the coordinate indexed by $w$, using the truth table of the $j$th bit, returns the sign encoding of $w_j$.

**Proof.** Let $x$ be the $[0m\mathbb F_2$-valued vector obtained by decoding the coordinate truth table. At the position indexed by $w$, its encoding is the value of that truth table there, hence is the sign encoding of $w_j$ (`coordinateTruthTable_apply_index`). The inverse relationship between encoding and decoding gives this first equality. The local correction therefore evaluates to the product of the sign encoding of $y$ at that position and the encoding of the sum of $x$ and $y$ there. Since encoding turns addition over $[0m\mathbb F_2$ into multiplication of signs (`signEncode_add`), this product is $sigl(s\,s(w_j)igr)$, where $s$ is the encoding of the corresponding coordinate of $y$. Sign units satisfy $s^2=1$, so the product reduces to $s(w_j)$, as required.

**Key facts.** `FABL.coordinateTruthTable_apply_index`, `FABL.signEncode_add`.
