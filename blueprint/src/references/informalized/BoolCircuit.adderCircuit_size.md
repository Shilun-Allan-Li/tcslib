<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.adderCircuit_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adder Circuit Size

**Claim.** For every natural number $n$, the size of the adder circuit on $n$ input vertices is $n+15\lfloor n/3\rfloor+4$.

**Proof.** The circuit size is the number of input vertices plus the number of gates. Expanding the adder-gate construction, the initial two constant gates contribute two gates, each of the $n/3$ bit blocks contributes fifteen, and the final output stage contributes two more. Thus there are $15(n/3)+4$ gates, giving total size $n+15(n/3)+4$, as claimed.
