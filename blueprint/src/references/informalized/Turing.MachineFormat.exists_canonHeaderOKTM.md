<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonHeaderOKTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Header Validity Test

**Claim.** For every machine format $F$, a finite Boolean Turing machine computes the one-bit answer indicating whether the input has a valid pair parse whose parsed header is canonical, in time linear in the input length.

**Proof.** Use the linear-time pair-validity test (`Turing.FinTM.computesFunInTime_pairValid`), the linear-time test for whether the canonical header bits end in true (or are empty) (`Turing.MachineFormat.exists_canonHeaderBitsTM`), and a linear-time machine that outputs the constant false word (`Turing.FinTM.computesFunInTime_const`). Combine them by conditional computation (`Turing.FinTM.computesFunInTime_cond`): test pair validity first, and on failure output false; on success output the canonical-header test. The resulting conditional output agrees with the desired predicate because `canonHeaderOK` is precisely pair validity conjoined with that header test. The conditional-computation bound is a constant times the sum of the component time bounds and one, hence is bounded by a constant multiple of $|\alpha|+1$. Finally, computation can be extended to any larger time bound without changing its result (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_pairValid`, `Turing.MachineFormat.exists_canonHeaderBitsTM`, `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.computesFunInTime_cond`, `Turing.FinTM.ComputesInTime.mono`.
