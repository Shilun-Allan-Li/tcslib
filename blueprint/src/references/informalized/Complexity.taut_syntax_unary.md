<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary-State Syntax Scan

**Claim.** For every finite binary string $x$, the syntax scan from the unary-index state accepts exactly when, after its maximal initial run of $1$s, the remaining suffix starts with $0$ and another bit, and the scan from the clause state accepts the suffix following those two bits.

**Proof.** Induct on $x$. The empty word gives the stated equality directly. If $x$ begins with $1$, the scan-cons identity says that processing this bit leaves the scanner in the unary state, while removing the initial $1$ leaves the same remainder after `takeTrues`; the induction hypothesis therefore applies. If $x$ begins with $0$, split on whether any further bit remains. With fewer than two bits, both sides reject. With at least two bits, the scanner moves from unary to polarity on the first $0$, then to clause on the next bit, so acceptance is exactly acceptance of the suffix after those two bits from the clause state.

**Key facts.** `Complexity.taut_syntax_cons`.
