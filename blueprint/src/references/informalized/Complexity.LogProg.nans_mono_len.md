<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.nans_mono_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Answer Length

**Claim.** Under the stated halting hypothesis, an answer witnessed by a choice sequence of length $N'$ exists exactly when it is witnessed by one of length $N$, whenever $N\le N'$.

**Proof.** Suppose first that a length-$N'$ sequence witnesses answer $b$. Keep only its first $N$ bits. The halting hypothesis says that every length-$N$ sequence has halted by then. Consequently, appending any further choices after those first $N$ bits leaves the configuration unchanged (`narun_append_of_halted`); in particular, the truncated sequence already has the same recorded answer as the original. Conversely, extend a witnessing length-$N$ sequence by $N'-N$ arbitrary bits. The halting hypothesis again guarantees that the configuration after the first $N$ choices is halted, so the added suffix changes nothing. The extended sequence has length $N'$ and still witnesses $b$.

**Key facts.** `Complexity.LogProg.narun_append_of_halted`.
