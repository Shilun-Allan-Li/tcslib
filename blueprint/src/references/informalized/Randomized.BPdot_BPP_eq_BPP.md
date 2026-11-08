<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPOperator.lean :: Randomized.BPdot_BPP_eq_BPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP closure under reductions

**Claim.** The class of languages that reduce by a many-one reduction to a language in BPP is exactly BPP.

**Proof.** For the inclusion from the reduction closure into BPP, take a language reducing to some BPP language. Randomized polynomial time is preserved under such reductions: the reduction-closure theorem (\texttt{Randomized.InBPP.of_randReducible}) puts the source language in BPP. Conversely, every BPP language reduces to itself, so it belongs to the reduction closure by the identity reduction (\texttt{Randomized.subset_BPdot}). These two inclusions give the equality.

**Key facts.** `Randomized.InBPP.of_randReducible`, `Randomized.subset_BPdot`.
