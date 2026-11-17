<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.moveInputPos_val_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Clamped Head Movements

**Claim.** Under the stated agreement of positions and bounds, moving either position by the same sign and clamping at its respective boundary gives equal values; the resulting value is at most $p+1$.

**Proof.** The sign lies between $-1$ and $1$, so after adding it to $p$ and converting to a natural number, the result is at most $p+1$. By the formula for clamped movement (`Turing.NDTM.moveInputPos_val`), each moved value is the minimum of this converted result and the corresponding upper boundary. The positions have the same value. If $p\le n'$, then the smaller interval's upper boundary $n'+1$ is at least the converted result, so both minima equal that result. If instead $n'=n$, the two upper boundaries coincide, and hence the minima agree directly. In either case the common result is at most $p+1$, as just shown.

**Key facts.** `Turing.NDTM.moveInputPos_val`.
