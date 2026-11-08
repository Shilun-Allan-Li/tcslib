<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.haltsWithin_of_codes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting within the code bound

**Claim.** If every length-$T$ choice string halts the machine and the space and code bounds hold, then every length-$V$ choice string also halts it.

**Proof.** Suppose, for contradiction, that a choice word $w$ of length $V$ ends in a nonhalting configuration. Consider the $V+1$ configurations reached after the prefixes $w.take(j)$, for $0\le j\le V$. Each stays within the space window (`inWin_run`), and its code lies below $2^{K(s+\ell(|x|)+1)}\le V$ (`cfgCode_lt`). Thus these $V+1$ codes take values in a set of only $V$ codes. The finite pigeonhole principle gives indices $i_0<j_0$ with equal codes.

We show that such a repeated code forces a contradiction. Put $u=w.take(i_0)$ and let $v$ be the segment from position $i_0$ through position $j_0-1$. Then $u$ followed by $v$ is the prefix of length $j_0$, and $v$ has positive length. The equal codes, together with the fact that both reached configurations are in the space window, imply that their core configurations agree (`coreSum_eq_of_code_eq`). The core records the state and transition-relevant configuration data, and running the same further word preserves equality of cores (`coreSum_runWith`). It follows by induction on $m$ that after $u$ followed by $m$ copies of $v$, the core is still the core after $u$: the case $m=0$ is immediate, and the successor case uses the repeated-segment equality and preservation under running a word. Choose $m=T$. Since $v$ is nonempty, the word $u$ followed by $T$ copies of $v$ has length at least $T$. Halting within length $T$ implies halting on this longer word as well (`HaltsWithin.mono`); but its final state agrees with the state after $u$ by the core equality. That state cannot be halted: if it were, the original word $w$ would also halt, since a halted configuration remains unchanged under every continuation (`runWith_of_halt`). This contradiction rules out the repeated-code pair, and hence the assumed nonhalting word. Therefore every length-$V$ word halts.

**Key facts.** `Complexity.Codec.cfgCode_lt`, `Randomized.BPLInP.inWin_run`, `Randomized.BPLInP.coreSum_eq_of_code_eq`, `Turing.NDTM.coreSum_runWith`, `Turing.NDTM.runWith_append`, `Turing.NDTM.HaltsWithin.mono`, `Turing.NDTM.runWith_of_halt`.
