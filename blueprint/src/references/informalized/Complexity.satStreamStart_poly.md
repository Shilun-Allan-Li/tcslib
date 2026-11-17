<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamStart_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Startup Encoding

**Claim.** The function mapping each bit string $x$ to the encoded startup state for $x$ is computable by a finite Turing machine in time $C(|x|+1)^c$ for some natural numbers $C$ and $c$.

**Proof.** Construct polynomial-time procedures for the two possible startup encodings. In the valid-syntax branch, the fresh-cursor component is the unary encoding of the decoded formula's variable count, which is polynomial-time computable; the consumed-length and phase components are empty unary strings. Pairing polynomial-time computable strings preserves polynomial-time computability, so these components give the encoded valid-branch state. In the invalid-syntax branch, the fresh-cursor and phase components are empty, while the consumed-length component is the unary encoding of the input length; this branch is also polynomial-time computable. Finally, the syntax test itself is polynomial-time computable, and a polynomial-time conditional combines the two branch procedures into the startup encoding.

**Key facts.** `Complexity.satSyntax_poly`, `Complexity.sat_pt_numVars`, `Complexity.sat_pt_const`, `Complexity.sat_pt_pair`, `Complexity.sat_pt_unaryLength`, `Complexity.sat_pt_cond`.
