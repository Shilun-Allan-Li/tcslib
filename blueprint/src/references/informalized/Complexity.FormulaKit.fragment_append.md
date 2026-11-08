<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/FormulaKit/Emit.lean :: Complexity.FormulaKit.fragment_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fragment of a Concatenation

**Claim.** For any two CNF formulas $\varphi$ and $\psi$ over natural-number variables, the binary fragment of their concatenation is the concatenation of their binary fragments.

**Proof.** The fragment is formed by mapping each clause to its binary encoding, with the clause marker prefixed, and concatenating those encodings in list order. Applying this operation to the concatenated clause list therefore gives the encodings from $\varphi$ followed by those from $\psi$. Thus $\operatorname{fragment}(\varphi++\psi)=\operatorname{fragment}(\varphi)++\operatorname{fragment}(\psi)$.
