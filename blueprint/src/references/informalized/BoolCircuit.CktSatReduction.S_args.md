<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.S_args -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Argument encoding and transducer output

**Claim.** For every finite list of natural numbers $\mathrm{args}$ and every bit string $r$, the transducer started in state $a$ on the encoded list followed by $r$ has the same output as the transducer started in state $g$ on $r$.

**Proof.** Induct on the list of arguments. For the empty list, its encoding is the terminator bit; processing that bit from state $a$ moves the transducer to state $g$ without output, so the remaining output is exactly the output from state $g$ on $r$.

For a nonempty list with first entry $a_0$ and remainder $\mathrm{args}$, the encoding begins with the list marker, followed by the unary encoding of $a_0$, then the encoding of the remainder and $r$. The transition on the marker moves from state $a$ to the unary-scanning state. Each true bit in the unary encoding leaves that state unchanged and emits no output, so the unary block can be skipped without changing the transducer’s output or state. The terminating false bit moves it to the state that begins processing the rest of the encoded list in the same way as state $g$. Apply the induction hypothesis to the remaining arguments and suffix $r$ to obtain the claimed equality.

**Key facts.** `BoolCircuit.CktSatReduction.S_cons`, `BoolCircuit.CktSatReduction.S_ones`.
