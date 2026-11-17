<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonStrip_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Removing a trailing run of ones

**Claim.** If every bit of $tail$ is $1$, then removing all trailing ones from $u++[false]++tail$ leaves exactly $u++[false]$.

**Proof.** Reverse the concatenated word. The reversed suffix $tail.reverse$ consists entirely of ones, by the hypothesis that every bit of $tail$ is true. Thus dropping the initial run of ones removes precisely that reversed suffix; the next bit is the false separator, so the remaining reversed word is $(u++[false]).reverse$. Reversing back gives $u++[false]$.
