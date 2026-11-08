<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.stages_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Cleaning Stages

**Claim.** Under the tape-support and interval hypotheses, the cleaning machine can run from stage $i$ through the remaining $n$ stages to stage $k$, keeping every work-tape head within absolute position $B$ throughout.

**Proof.** First establish that all head positions represented at any stage are bounded by $B$. For a tape not yet cleaned, the hypotheses bound its original head position between $a$ and $b$, and the margins $-B\le a-1$ and $b+1\le B$ imply its absolute value is at most $B$; already-cleaned tapes have head position zero. The same bound applies to the marked-tape heads, so each stage configuration satisfies the required position bound (`PB_ccfg`). Proceed by induction on the number $n$ of stages remaining. If $n=0$, the equation $i+n=k$ gives $i=k$, and the starting stage already is the target stage; the bound follows from the established head bounds. For the successor case, clean tape $i$ using `clean_tape`. Its hypotheses follow from the given interval, support, and marked-tape conditions, while the global head bound supplies its position-bound premise. This produces a finite run that stays within the bound and leaves tape $i$ cleared with head at zero. The resulting configuration is exactly stage $i+1$: this identification follows by updating the stage data at index $i$. Apply the induction hypothesis to the remaining stages. Concatenating the bounded first run with the bounded continuation preserves the bound throughout (`runFrom_forall_append`), and the run composition law (`runFrom_add`) shows the combined run ends at stage $k$.

**Key facts.** `Complexity.LogProg.PB_ccfg`, `Complexity.LogProg.clean_tape`, `Complexity.LogProg.runFrom_forall_append`, `Turing.MultiTapeTM.runFrom_add`.
