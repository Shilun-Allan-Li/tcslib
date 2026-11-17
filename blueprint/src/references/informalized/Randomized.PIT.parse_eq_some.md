<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.parse_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from a successful parse

**Claim.** If parsing a bit string $l$ with the gate parser returns gate $g$ and remainder $l'$, then $l$ is the encoding of $g$ followed by $l'$.

**Proof.** First establish that any successful unary-natural parse reconstructs its input: if decoding $w$ returns $j$ and remainder $r$, then $w$ is the encoding of $j$ followed by $r$. The decoder characterization `decodeNat_eq` identifies success with the presence of a false bit, and `eq_encodeNat_of_hasFalse` gives precisely this reconstruction. Next, for a successful binary-gate parse, unfold the parser: both unary fields must decode successfully, say to $j$ and $k$, with final remainder $l'$. Applying the reconstruction fact to each field shows that the input is the encoding of $j$ followed by the encoding of $k$ and then $l'$, with associativity of concatenation fixing the order. Finally split on the parser's leading tag. The variable case uses the unary reconstruction; the constant-one case has no fields to decode; and each of the three binary tags uses the binary reconstruction. In every successful branch the tag and reconstructed fields are exactly the encoding of the returned gate. Tags that cannot parse successfully are impossible under the hypothesis.

**Key facts.** `Complexity.BinArith.decodeNat_eq`, `Complexity.BinArith.eq_encodeNat_of_hasFalse`.
