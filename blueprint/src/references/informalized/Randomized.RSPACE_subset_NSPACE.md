<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.RSPACE_subset_NSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Space Is Nondeterministic Space

**Claim.** For every space bound $s$, every language in $\mathrm{RSPACE}(s)$ belongs to $\mathrm{NSPACE}(s)$.

**Proof.** Take a language $L$ in $\mathrm{RSPACE}(s)$, witnessed by a constant $c$, a finite machine $N$, and the assertion that $N$ randomized-decides $L$ within space $c s$. The fact that a randomized space decider is also a nondeterministic space decider ( `RDecidesInSpace.decidesInSpace`) supplies a decider using the same machine and the same space bound. Thus the same $c$ and $N$ witness that $L\in\mathrm{NSPACE}(s)$.

**Key facts.** `Turing.FinNDTM.RDecidesInSpace.decidesInSpace`.
