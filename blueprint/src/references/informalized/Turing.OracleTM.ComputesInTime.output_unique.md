<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.ComputesInTime.output_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Computed Output

**Claim.** If the same machine with the same oracle halts on input $x$ with outputs $w$ and $w'$ at possibly different times, then $w=w'$.

**Proof.** Let $m$ be the larger of the two halting times. By monotonicity of computation time, both computations halt at time $m$, with their respective outputs still $w$ and $w'$. At that common time, both outputs are the output field of the same configuration reached by running the machine from the same initial configuration. Those fields are equal, so $w=w'$.

**Key facts.** `Turing.OracleTM.ComputesInTime.mono`.
