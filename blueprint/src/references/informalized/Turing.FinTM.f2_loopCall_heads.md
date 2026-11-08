<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopCall_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop Call Head Position Bound

**Claim.** If every work-tape head of $\mathrm{fuel}$ lies in $[-B,B]$, then every work-tape head of the specified loop-call configuration also lies in $[-B,B]$.

**Proof.** Separate the work-tape indices into the final added tape and the padded tapes. The final added tape is the capture tape, whose head is the length of an empty prefix and hence is zero, which lies in $[-B,B]$. Among the padded tapes, the body tapes inherit their heads from the seam configuration; those heads are zero. The extra body flag tape also has head zero. The single buffer tape used for $\mathrm{word}$ has head zero as well. The remaining padded tapes are precisely the tapes of $\mathrm{fuel}$, so their heads satisfy the claimed bounds by the hypothesis. Since $B$ is nonnegative, zero lies in the interval, and all cases give the result.
