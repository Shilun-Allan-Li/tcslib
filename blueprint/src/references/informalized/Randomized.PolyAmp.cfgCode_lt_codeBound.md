<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.cfgCode_lt_codeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Code Bound

**Claim.** For every finite nondeterministic Turing machine $N$, Boolean input word $x$, natural number $S$, and configuration $C$ of $N$ on $x$, the code of $C$ using window size $S$ is less than $2^{K(N)(S+\log_2(|x|)+1)}$, with the quantities as specified in the statement.

**Proof.** By the configuration-code bound `cfgCode_lt`, the code of any configuration with window size $S$ is strictly less than $2^{K(N)(S+\log_2(|x|)+1)}$. The stated code bound is exactly this power of two, so the result follows directly.

**Key facts.** `Complexity.Codec.cfgCode_lt`.
