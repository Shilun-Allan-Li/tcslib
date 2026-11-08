<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.exists_canonOffsetTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Canonical Offset

**Claim.** There are a finite Boolean Turing machine and a constant such that on each input word $w$ the machine halts with output equal to the canonical offset of $w$, in time linear in $|w|+1$.

**Proof.** First compute the bits of the input length, using the linear-time length-bits machine (`Turing.FinTM.computesFunInTime_lengthBits`). Apply the linear-time canonical-count machine (`Turing.MachineFormat.exists_canonCountTM`) to those bits. The machines can be composed with a linear bound in the length of the intermediate output (`Turing.FinTM.computesFunInTime_comp`); since the bit representation of the input length has length at most the input length, the composed computation still has a linear bound in $|w|+1$. Then prepend the single true bit using the linear-time prepend machine (`Turing.FinTM.computesFunInTime_prepend`) and compose again. The result is exactly the canonical offset, by its definition. The composition bounds have fixed multiplicative constants and are bounded by one fixed constant times $|w|+1$; if necessary, extend the run to that bound (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits`, `Turing.MachineFormat.exists_canonCountTM`, `Turing.FinTM.computesFunInTime_comp`, `Turing.FinTM.computesFunInTime_prepend`, `Turing.FinTM.ComputesInTime.mono`.
