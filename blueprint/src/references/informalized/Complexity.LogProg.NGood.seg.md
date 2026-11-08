<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMRun.lean :: Complexity.LogProg.NGood.seg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Good Run Segments

**Claim.** If all runs from $C$ through length $S$ satisfy $\mathrm{box}$ and every length-$S$ run reaches $C'$, while $C'$ has the good-run properties through length $T$, then $C$ has them through length $S+T$.

**Proof.** For any choice word of length at least $S$, split it into its first $S$ choices and the remaining suffix. The run concatenation law says that running the whole word is the same as running the suffix from the configuration reached after the first segment. By hypothesis that intermediate configuration is $C'$, so the full run agrees with the suffix run from $C'$ (`Turing.NDTM.runWith_append`). For a word of length at most $S+T$, if it is shorter than $S$, the assumed box condition from $C$ applies directly. If it has length at least $S$, the suffix has length at most $T$, so the box condition from $C'$ and the run equality give the desired box property. Finally, a word of length exactly $S+T$ has a suffix of length exactly $T$; the terminal condition from $C'$ supplies halting and $Q$, and the same equality transfers both to the run from $C$.

**Key facts.** `Turing.NDTM.runWith_append`.
