<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.FinTM.ComputesFunInTime.computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time-Bounded Computation Implies Computation

**Claim.** If the machine halts with output $f(x)$ within $T(|x|)$ steps on every input $x$, then it computes $f$.

**Proof.** Fix an input $x$. The hypothesis gives computation of $f(x)$ at the particular time $T(|x|)$. Taking that time as the witness in the definition of computation proves the claim for $x$, and hence for every input.
