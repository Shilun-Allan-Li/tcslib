<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_polyCanonizer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Canonical Serialization

**Claim.** For every machine format $F$, there is a finite Boolean Turing machine that outputs the serialization of the code decoded from any input $\alpha$, and halts within a polynomial bound in $|\alpha|+1$.

**Proof.** The canonical decider (`Turing.MachineFormat.exists_canonDecider`) determines whether the input is accepted by the format's canonical scan. A false answer certifies that decoding yields the fallback code; a true answer certifies that the scan succeeds. In parallel, the canonical stripping machine (`Turing.MachineFormat.exists_canonStripTM`) computes the stripped input, while a constant-output machine (`Turing.FinTM.computesFunInTime_const`) supplies the serialization of the fallback code. Combine these by conditional computation (`Turing.FinTM.computesFunInTime_cond`): on acceptance output the stripped word, and otherwise output the fallback serialization. The branch output is correct in either case. In the false case this follows from the decider's fallback guarantee. In the true case it follows from `Turing.MachineFormat.canonStrip_of_scan`, which identifies the stripped input with the serialization of the decoded code when the scan succeeds. The conditional machine's time is bounded by a constant times the decider time plus the larger branch time and one. Each of these is polynomial in $|\alpha|+1$, so choosing an exponent large enough to dominate all branch exponents and then enlarging the coefficient gives a single bound $d(|\alpha|+1)^d$. Monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) permits extending the run to this bound.

**Key facts.** `Turing.MachineFormat.exists_canonDecider`, `Turing.MachineFormat.exists_canonStripTM`, `Turing.FinTM.computesFunInTime_const`, `Turing.FinTM.computesFunInTime_cond`, `Turing.MachineFormat.canonStrip_of_scan`, `Turing.FinTM.ComputesInTime.mono`.
