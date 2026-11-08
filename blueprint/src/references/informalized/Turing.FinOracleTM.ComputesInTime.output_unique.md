<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleFinite.lean :: Turing.FinOracleTM.ComputesInTime.output_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of computed output

**Claim.** If the finite-state deterministic oracle machine halts on input $x$ with output $w$ after $t$ steps and with output $w'$ after $t'$ steps, then $w=w'$.

**Proof.** Regard the finite-state oracle machine as its underlying oracle Turing machine. The oracle-machine output-uniqueness theorem states that any two halting runs on the same input with the same oracle have equal outputs, regardless of their halting times (\texttt{Turing.OracleTM.ComputesInTime.output_unique}). Applying it to the two assumed computations yields $w=w'$.

**Key facts.** `Turing.OracleTM.ComputesInTime.output_unique`.
