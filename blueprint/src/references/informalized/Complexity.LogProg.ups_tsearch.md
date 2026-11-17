<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathSearch.lean :: Complexity.LogProg.ups_tsearch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Target Encoding Search

**Claim.** Under the stated register bounds, search-range conditions, and candidate-processing and empty-search hypotheses, the target-search stage has acceptance probability $q$ and satisfies the termination and register-bound conditions.

**Proof.** Induct on the number $dd=\sigma.n-\sigma.u$ of remaining candidates. If $dd=0$, then $\sigma.u=\sigma.n$, so the search interval is empty. The empty-search hypothesis gives $q=0$, and the program’s equality test rejects; the rejecting state has probability zero (`ups_rej`), so the desired semantics follow (`PSem.jeq_pos`).

For the successor case, the interval is nonempty. The equality test takes its negative branch, and the program clears its scratch register and copies the current pointer into the target-search registers (`ups_cp`). It compares the binary expansion of the current candidate at that pointer. If the plain encoding matches, the program proceeds to the candidate-processing stage, whose probability is $q$ by hypothesis. If it does not match, the program advances the candidate counter and returns to the search stage. The remaining interval has one fewer candidate, so induction applies. To verify its empty-search condition, any matching candidate in the old interval is either the current candidate, ruled out by this failed comparison, or belongs to the shortened interval. Register bounds are maintained by the clear and copy steps and by the assumed bound on every successor state; the comparison’s matching and mismatching continuations are summarized by `ups_tcmp`. The counter update preserves semantics through `PSem.inc`, while the clear and equality branches use `PSem.clr` and `PSem.jeq_neg`.

**Key facts.** `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.ups_rej`, `Complexity.LogProg.PSem.jeq_neg`, `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.ups_cp`, `Complexity.LogProg.ups_tcmp`, `Complexity.LogProg.PSem.inc`.
