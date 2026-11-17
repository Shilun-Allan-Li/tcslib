<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.incFixed_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cases for Fixed-Width Increment

**Claim.** Every Boolean word is either all true and has undefined fixed-width increment, or has a unique initial run of $j$ true values followed by false and a suffix, with increment obtained by changing those $j$ true values to false and that false to true.

**Proof.** Induct on the word. The empty word is entirely true and its increment is undefined. For a nonempty word, if its first bit is false, take $j=0$ and the remaining word as the suffix; the increment definition immediately gives true followed by that suffix. If the first bit is true, apply the induction hypothesis to the tail. When the tail is entirely true, adjoining the initial true shows the whole word is entirely true, and the increment remains undefined. Otherwise the tail has $j$ initial true bits followed by false and a suffix; adjoining the initial true gives $j+1$ initial true bits, and the recursive increment changes these to $j+1$ false bits followed by true and the same suffix.
