<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_load_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol at a specified position

**Claim.** The loader configuration whose physical input head is at position $i+1$ reads the optional symbol $y[i]$, including the absent symbol when $i=|y|$.

**Proof.** The loader configuration has input position with value $i+1$. The general input-position lemma says that any configuration with this position, provided $i\le |y|$, reads exactly the optional list entry $y[i]$ (`Turing.FinTM.inputSymbol_at`). Applying that fact gives the claim directly.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
