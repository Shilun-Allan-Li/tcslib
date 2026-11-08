<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup of the Reverse Host

**Claim.** For a choice word of length $2|x|+2$, running the reverse host from its initial configuration on $x$ reaches the guessing-phase configuration with the input-normalized scheduler initialized on $x$ and empty guessed word.

**Proof.** First run the host on the prefix of $w$ of length $|x|$. The input copy phase fills the assembly buffer with $x$ and reaches loader state $0$ with the assembly head at the right boundary (`Complexity.b2_initial`, `Complexity.b2_copy_run`). The remaining suffix has length $|x|+2$, by the assumed total length. Write it as a first bit followed by a tail of length $|x|+1$. Split the full run at this prefix and then at the first bit (`Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`). The boundary transition `Complexity.b2_copy_done` moves the host into loader state $1$ at the right end of the input. The remaining tail then performs the complete rewind and dispatch to the guessing phase, by `Complexity.b2_rewind_run` with index $|x|$.

**Key facts.** `Complexity.b2_initial`, `Complexity.b2_copy_run`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Complexity.b2_copy_done`, `Complexity.b2_rewind_run`.
