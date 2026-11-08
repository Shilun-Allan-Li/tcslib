<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean :: Complexity.LogProg.CleanRun.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Work-Tape Bound

**Claim.** A clean run satisfying work-tape head bound $B$ also satisfies any larger bound $B'$, provided $B\le B'$.

**Proof.** Keep the same halting time and the same run. Its halting state, output, blank work tapes, and zero head positions are therefore unchanged. At every time up to the halting time, each head's absolute position is at most $B$ by hypothesis, hence at most $B'$ by transitivity of the order.
