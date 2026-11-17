<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.exists_not_timeConstructible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A non-time-constructible dominating function

**Claim.** There is a function T that dominates the identity function pointwise but is not time constructible.

**Proof.** Use the function `ntcT` constructed earlier. Its values dominate n because `ntcT n` is n plus a natural number, so n≤ntcT(n). The theorem `ntc_not_timeConstructible` establishes that this function fails the stated time-constructibility condition. These two facts give the required function.

**Key facts.** `Complexity.ntc_not_timeConstructible`.
