<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_incFixed_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cases for Fixed-Width Increment

**Claim.** Every Boolean word is either all true, in which case its fixed-width increment is undefined, or consists of a run of true bits followed by false and a suffix, in which case increment changes that run to false bits and that false bit to true, leaving the suffix unchanged.

**Proof.** Induct on the word. The empty word is the all-true word and its increment is undefined. If a nonempty word begins with false, it already has the second form with a run of length zero, and increment changes that first bit to true. If it begins with true, apply the induction hypothesis to the tail. When the tail is all true, the whole word is all true and repeated propagation of the increment rule leaves it undefined. Otherwise the tail has a first false after some run of true bits; adding the leading true extends that run by one, and the recursive increment rule changes this longer run to false bits before the first false becomes true, leaving the rest untouched.
