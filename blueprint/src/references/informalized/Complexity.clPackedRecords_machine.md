<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPackedRecords_machine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time production of packed records

**Claim.** For each finite-state Boolean Turing machine $M$ and natural numbers $C,e,c,A,d$, some finite-state Boolean Turing machine computes the packed-records function in polynomial time, and its output length is bounded by a polynomial in the input length.

**Proof.** The native construction theorem (`Complexity.clPackedRecords_native`) supplies a machine $H$ and constants $a,r$ for which the packed-records function is computed within $a(|x|+1)^r$ steps on every input $x$. To bound output length, apply the characterization of computation in time (`Turing.FinTM.computesInTime_iff`): at that time, the output of $H$ is exactly the packed-records word. A machine's output after $t$ steps has length at most $t$ (`Turing.MultiTapeTM.output_length_le`). Hence the word's length is at most $a(|x|+1)^r$, as required.

**Key facts.** `Complexity.clPackedRecords_native`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`.
