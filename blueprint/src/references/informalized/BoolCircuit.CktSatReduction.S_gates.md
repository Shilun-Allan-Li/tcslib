<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.S_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output after encoded gates

**Claim.** For every finite list of gates and every finite bit string $r$, the transducer started in state $g$ outputs exactly $r$ on the encoding of the gate list followed by $r$.

**Proof.** Proceed by induction on the gate list. For the empty list, its encoding is the single delimiter bit $0$. Starting in state $g$, reading that bit moves the transducer to state $o$; the output on the suffix is therefore exactly $r$, since $o$ is absorbing and emits every bit it reads (`S_o`). For a nonempty list, write its first gate as a label followed by its encoded argument list, with the remaining gates after it. Consider the three possible labels. The two bits encoding AND or OR, and the two bits encoding NOT, move the transducer through the corresponding gate-reading states and then into state $a$. Processing the encoded arguments from $a$ returns it to state $g$ with no output (`S_args`). The induction hypothesis then says that processing the remaining encoded gates followed by $r$ from $g$ outputs $r$. The one-bit output rule (`S_cons`) accounts for each input bit along these transitions; the gate-reading states emit nothing. Thus in every label case the whole gate encoding is suppressed and the remaining gates and suffix produce exactly $r$.

**Key facts.** `BoolCircuit.CktSatReduction.S_cons`, `BoolCircuit.CktSatReduction.S_args`, `BoolCircuit.CktSatReduction.S_o`.
