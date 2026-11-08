<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_takeWhile_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False-word prefix scan length

**Claim.** For every natural number $n$, scanning the length-$n$ word consisting entirely of false values with the predicate that accepts false values gives a prefix of length $n$.

**Proof.** Induct on $n$. For $n=0$, the word is empty, so the scanned prefix has length zero. For the successor case, the word begins with false, which satisfies the predicate; removing that first element leaves the length-$n$ all-false word. By the induction hypothesis its scan has length $n$, and including the accepted first element gives length $n+1$.
