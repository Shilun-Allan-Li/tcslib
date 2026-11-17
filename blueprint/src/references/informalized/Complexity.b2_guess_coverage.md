<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_guess_coverage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coverage of scheduler guesses

**Claim.** When the input-normalized machine derived from $S$ computes $v$ on $x$ in exactly $T$ steps and is active before then, every choice word of length $T$ leads the host to the scheduler's time-$T$ guessing configuration with a guessed word of length $|v|$, and every word of that length is obtained from some choice word.

**Proof.** The continuous-guessing machine has both directions of coverage: every length-$T$ choice word produces a guessed word of length $|v|$, and every such guessed word is realized by some choice word (`cont_guess_coverage`). To transfer this statement to the host, take any such choice word $w$ and guessed word $u$. The initial configurations agree after identifying the continuous guesser with the host's guessing phase (`cont_guess_initial`). The run formula for the continuous guesser (`cont_guess_run`) describes its state after $w$ and its accumulated guessed word. Meanwhile, the host's guessing-run formula (`b2_guess_run`), using the hypothesis that the scheduler stays active at all earlier times, gives the corresponding host state and guessed word. Equality of the continuous-guessing configurations forces equality of their guessed words (`b2_guess_word_injective`). Thus each continuous-guessing witness transfers to the host, in both coverage directions.

**Key facts.** `Complexity.cont_guess_coverage`, `Complexity.cont_guess_initial`, `Complexity.cont_guess_run`, `Complexity.b2_guess_run`, `Complexity.b2_guess_word_injective`.
