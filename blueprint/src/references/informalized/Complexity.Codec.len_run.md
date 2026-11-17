<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.len_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input length scan

**Claim.** The length scan reaches the first prefix-scan instruction with every register unchanged except $r_L$, which is set to $|y|$, and all configurations before the final one satisfy the run guard with bound $B$.

**Proof.** Apply the input-length scan lemma (`inputLength_loop`) with $r_L$ as the scanned register. At each scan position $n$, the program queries whether the input has a symbol at position $n$. The oracle answers positively exactly when $n<|y|$ (`orc_len`). Consequently, the scan increments $r_L$ once for each input position and stops at $|y|$. The initial value is no greater than $|y|$, so the scan reaches this endpoint; the bound $|y|\le B$ ensures that the register remains within the guard throughout. All other registers are untouched, and the scan lemma gives the required run-guard property at every pre-final configuration.

**Key facts.** `Complexity.Codec.orc_len`, `Complexity.LogProg.inputLength_loop`.
