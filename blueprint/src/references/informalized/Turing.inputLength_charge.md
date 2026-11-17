<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.inputLength_charge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digit Charge

**Claim.** Under the stated forms of the binary digits of $n$ and $n+1$, the number of ones in the digits of $n+1$, plus $p$, equals the number of ones in the digits of $n$ plus one; moreover, $p$ is less than the length of the digits of $n+1$.

**Proof.** Substitute the given form of the digits of $n+1$. In the first case for $n$, its digits contain $p$ ones followed by a zero and the unchanged suffix $v$, while the new digits contain $p$ zeros followed by a one and that suffix. Counting ones therefore removes the $p$ leading ones and adds one, giving the asserted equality. In the second case, the old digits are exactly $p$ ones and the suffix is empty, whereas the new digits are $p$ zeros followed by one one. The same count identity follows. In both cases, the new digit list begins with a block of length $p$ and has at least one further digit, so its length is strictly greater than $p$.
