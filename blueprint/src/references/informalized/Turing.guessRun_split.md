<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRun_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting a Boolean word at a given position

**Claim.** If $L<|w|$, then $w$ can be written as a prefix $a$, followed by one Boolean $b$, followed by a suffix $r$, with $|a|=L$.

**Proof.** Take $a$ to be the first $L$ entries of $w$, let $b$ be its entry at position $L$, and let $r$ be the entries after position $L$. The inequality $L<|w|$ ensures that this entry exists. The list decomposition into prefix, selected entry, and remaining suffix gives $w=a++[b]++r$, and the prefix has length $L.
