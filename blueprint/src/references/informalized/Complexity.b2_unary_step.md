<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_unary_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Unary Normalization

**Claim.** Reinterpreting the normalized machine's successor configuration from $c$ gives the successor of $M$ from the unary reinterpretation of $c$.

**Proof.** If $c$ is halted, both machines leave it unchanged, so the claim follows directly. Otherwise let $q$ be its state. The normalized transition applies $M$'s transition at $q$ using the original input read with each present bit replaced by true. The unary-read identity (`Complexity.b2_unary_read`) says that this is precisely the read from the reinterpreted configuration; the work-tape symbols are unchanged. Hence both transitions choose the same action. Reinterpretation commutes with applying any fixed action (`Complexity.b2_unary_apply`), so the resulting configurations agree.

**Key facts.** `Complexity.b2_unary_apply`, `Complexity.b2_unary_read`.
