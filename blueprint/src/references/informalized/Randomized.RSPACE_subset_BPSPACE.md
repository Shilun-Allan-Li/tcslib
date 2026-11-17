<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.RSPACE_subset_BPSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Space Lies in Bounded-Error Space

**Claim.** For every space bound $s$, every language in $\mathrm{RSPACE}(s)$ belongs to $\mathrm{BPSPACE}(s)$.

**Proof.** Take a language in $\mathrm{RSPACE}(s)$ and its witnessing constant and finite randomized machine. The machine-level conversion from one-sided randomized space to bounded-error space preserves the same space bound and gives the required correct-answer probability on every input (Turing.FinNDTM.RDecidesInSpace.bpDecidesInSpace). Keeping the same constant and machine therefore witnesses membership in $\mathrm{BPSPACE}(s)$.

**Key facts.** `Turing.FinNDTM.RDecidesInSpace.bpDecidesInSpace`.
