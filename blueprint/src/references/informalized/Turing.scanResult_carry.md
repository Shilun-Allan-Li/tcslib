<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.scanResult_carry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Carry Scan Output

**Claim.** The two-pass carry scan returns the conjunction of the top predicate over the input word and changes exactly the initial top-true prefix and, when present, its first following symbol by applying next.

**Proof.** By the fact that a second keep scan leaves the first pass unchanged (`Turing.scanResult_keep`), it suffices to analyze the forward carry scan. Induct on the word. The empty word leaves the initial true carry unchanged and produces no symbols, giving the stated result. For a word with head γ, split according to whether top γ is true. If it is true, the carry remains active precisely when top γ holds, the head is changed to next γ, and the induction hypothesis describes the remaining scan; this extends the initial top-true prefix by γ. If top γ is false, the head is changed to next γ, the carry becomes false, and it stays false on the tail: once cleared, the scan returns that tail unchanged (`Turing.mealyRun_carry_clear`). Thus γ is the first symbol after the top-true prefix, and all later symbols remain unchanged. In both cases the final carry is the conjunction of top over the word, and the described output pieces agree with the takeWhile/dropWhile expression.

**Key facts.** `Turing.scanResult_keep`, `Turing.mealyRun_carry_clear`.
