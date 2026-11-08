<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_prevalidation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds from Successful Pair Decoding

**Claim.** If decoding $w$ gives $(x',u)$ and decoding $x'$ gives $(x,\mathrm{pad})$, then $|x|\le |w|$, and the length of the binary expansion of $C(2^{|x|+1})^c$ is at most $(|w|+1)^c$ plus the length of the binary expansion of $C$.

**Proof.** Successful decoding is reversible: whenever `pairDecode z = some (a,b)`, the original word is `pairEncode a b` (`Complexity.a3n_pair_inverse`). Applying this once to $w$ and once to $x'$ expresses both decoded words as their pair encodings. The encoding duplicates each bit of its first component and adds a delimiter before its second component, so these two identities imply $|x|\le |w|$ by direct length calculation. The stated bound on the binary-expansion length now follows from the general estimate for $n\le m$, applied with $n=|x|$ and $m=|w|$ (`Complexity.e3_bits_length_bound`).

**Key facts.** `Complexity.a3n_pair_inverse`, `Complexity.e3_bits_length_bound`.
