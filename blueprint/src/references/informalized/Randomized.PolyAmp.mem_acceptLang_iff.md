<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.mem_acceptLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance-Language Characterization

**Claim.** Under the stated space hypotheses, if configuration $C$ is reachable from the initial configuration, then the encoding of $x$, the code of $C$ at space bound $S$, and $S$ belongs to the acceptance language exactly when $C$ is halted and its output is $[1]$.

**Proof.** Reachability together with the space bound provides a configuration $D$ inside the window of size $S$ such that $D$ has the same core data as $C$ and has the same code as $C$ at that window size (`Reach.inWin`). Unfolding membership in the acceptance language, its encoded input belongs precisely when there is an in-window configuration $E$ with the specified code that is halted and has output $[1]$ (`mem_acceptLang`).

For the forward implication, take such an $E$. The in-window code-uniqueness result `coreSum_eq_of_code_eq` applies to $E$ and $D$, since their codes agree, and shows their core data agree. Combining this with the equality of the core data of $D$ and $C$, and using preservation of acceptance under equality of core data (`accepting_congr`), transfers the halted and accepting-output properties from $E$ to $C$.

Conversely, if $C$ is halted with output $[1]$, then `accepting_congr` transfers this property to $D$, whose code and window condition already satisfy the membership requirements. Taking $D$ as the witness proves membership.

**Key facts.** `Randomized.PolyAmp.Reach.inWin`, `Complexity.Codec.mem_acceptLang`, `Randomized.BPLInP.coreSum_eq_of_code_eq`, `Randomized.PolyAmp.accepting_congr`.
