<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_fuel_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Bounds After Fuel Capture

**Claim.** If every work-tape head of the fuel configuration lies in $[-N,N]$ and its output has length at most $N$, then every work-tape head in the captured fuel configuration lies in $[-N,N]$.

**Proof.** The capture adds a final tape whose head is placed at the length of the fuel configuration's output. This is nonnegative and at most $N$, so it lies in $[-N,N]$. All earlier tapes consist of the body-side padding tapes, whose heads are zero, followed by the fuel machine's original tapes, whose heads satisfy the assumed bound. Therefore every head in the captured configuration lies in the interval.
