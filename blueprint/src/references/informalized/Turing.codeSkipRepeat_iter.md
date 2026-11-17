<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codeSkipRepeat_iter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of a Partial Reader

**Claim.** For a partial reader $r$, iterating the operation that propagates failure and applies $r$ to a present string $n$ times, starting at $xs$, gives the same result as applying the reader successively $n$ times to the returned suffixes.

**Proof.** Induct on $n$, allowing the starting string to vary. At $n=0$, both sides are the present value $xs$. For the successor step, first apply $r$ to $xs$. If it fails, the iterated operation remains failed for every further iteration; the recursively defined reader also fails, as is seen by a second induction on the number of remaining iterations. If $r(xs)$ returns a string $ys$, the remaining computation is exactly the induction hypothesis applied to $ys$.
