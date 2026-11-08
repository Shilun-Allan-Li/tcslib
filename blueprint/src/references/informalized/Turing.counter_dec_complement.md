<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_dec_complement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrement and Complemented Increment

**Claim.** For every Boolean word $w$, decrementing it at fixed width gives the same optional word as complementing its bits, incrementing at that width, and complementing the result; failure due to overflow is preserved.

**Proof.** Induct on the word. The empty word gives the identity directly. For a word with head bit $b$ and tail $w$, split on whether $b$ is false or true. If $b$ is false, decrement flips that leading bit to true and retains the recursive decrement behavior on the tail; complementing first makes the leading bit true, so incrementing uses its recursive branch, and complementing the resulting word restores the same leading bit and tail behavior. If $b$ is true, decrement immediately changes it to false, while complementing first makes it false so incrementing immediately changes it to true; complementing that result returns false. In both cases the recursive identity from the induction hypothesis identifies the optional tail results, including the undefined case, so the whole optional words agree.
