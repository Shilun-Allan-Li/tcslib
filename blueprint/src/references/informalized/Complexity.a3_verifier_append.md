<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_verifier_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verifier on padded concatenations

**Claim.** If $|u|=2^{(|x|+1)^c}$, then $x$ followed by $u$ belongs to the padding verifier for $L$ at degree $c$ if and only if $x\in L$.

**Proof.** The concatenated word has length $|x|+2^{(|x|+1)^c}$, so the split equation with padding coefficient $1$ holds at split point $|x|$. By completeness of the split search (`a3_split_complete`), the verifier's search returns precisely that point. The verifier therefore tests whether the prefix of length $|x|$ of the concatenation belongs to $L$. That prefix is $x$, giving the stated equivalence.

**Key facts.** `Complexity.a3_split_complete`.
