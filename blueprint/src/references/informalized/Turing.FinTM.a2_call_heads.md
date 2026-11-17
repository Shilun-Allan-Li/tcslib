<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_call_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Bounds in a Captured Call

**Claim.** If the body and fuel configurations have all work-tape heads in $[-B,B]$, and the body's output has length at most $B$, then every work-tape head in the configuration formed by capturing the call also lies in $[-B,B]$.

**Proof.** Partition the captured configuration's tape indices into the final capture tape and the preceding tapes. On the final tape, the head is placed at the length of the body's output (the prefix is empty here). This position is nonnegative and at most $B$, so it lies in $[-B,B]$. Among the preceding tapes, the body's original tapes retain their head positions. Its added flag tape has head position zero. The remaining tapes include the extra word tape, also with head at zero, and the fuel machine's tapes, whose positions satisfy the assumed bounds. Thus every head in the captured configuration lies in the required interval.
