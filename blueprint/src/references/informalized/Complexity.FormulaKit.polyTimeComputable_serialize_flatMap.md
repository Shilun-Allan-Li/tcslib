<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Emit.lean :: Complexity.FormulaKit.polyTimeComputable_serialize_flatMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization of Indexed Formula Concatenation

**Claim.** If the count is polynomial-time computable in unary and the fragment encoding of each indexed formula is polynomial-time computable from the encoded pair, then the binary serialization of the concatenation of the formulas for indices below the count is polynomial-time computable.

**Proof.** First use the polynomial-time range-concatenation result with chunks $\operatorname{fragment}(G(x,i))$. The count hypothesis supplies its unary bound, and the assumed pair-input computation supplies each chunk, so concatenating these fragments over $0\le i<\operatorname{count}(x)$ is polynomial-time computable (`polyTimeComputable_flatMap_range`). Append the constant bit string $[\mathrm{false}]$, which is polynomial-time computable (`polyTimeComputable_const`), using closure under concatenation (`PolyTimeComputable.append`). This output is the desired serialization: the fragment of a concatenation of formulas is the concatenation of their fragments (`fragment_flatMap`), and serialization of a formula is its fragment followed by one false bit (`serialize_eq_fragment`).

**Key facts.** `Complexity.FormulaKit.polyTimeComputable_flatMap_range`, `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_const`, `Complexity.FormulaKit.serialize_eq_fragment`, `Complexity.FormulaKit.fragment_flatMap`.
