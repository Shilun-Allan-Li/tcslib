<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.xhat_eq_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank positions in a shifted word

**Claim.** The shifted word has no symbol at integer position $z$ exactly when $z<1$ or $|x|<z$.

**Proof.** Unfold the shifted-word lookup and split according to whether $1\le z$. If this inequality holds, the lookup is at the natural index corresponding to $z-1$; a list lookup is undefined exactly when that index is outside the list, which is equivalent to $|x|<z$. If $1\le z$ fails, the shifted word is blank by definition, and the integer-order alternatives give $z<1$. Together these cases yield the stated equivalence.
