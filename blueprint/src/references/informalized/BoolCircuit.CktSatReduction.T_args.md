<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.T_args -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transduction of encoded argument lists

**Claim.** For every finite list $A$ of natural numbers and bit string $r$, processing the encoding of $A$ followed by $r$ from state $a$ preserves the encoded list and processes $r$ from state $g$.

**Proof.** Induct on the list of natural numbers. For the empty list, its encoding is the delimiter $0$. From state $a$, that bit moves the transducer to $g$ and is unchanged by the bit-swapping rule; the suffix is consequently processed from $g$. For a nonempty list, its encoding begins with a marker $1$, followed by the unary encoding of its first number and then the encoding of the remaining list. From state $a$, the marker moves to state $u$. In state $u$, each of the consecutive unary ones leaves the state unchanged and is preserved. The fact that such a run is passed through unchanged while leaving the suffix to be processed from the same state is `T_ones`. The following delimiter $0$ moves the transducer to state $a$; it too is preserved. The induction hypothesis now applies to the encoding of the remaining numbers and the suffix. Together these steps show that the entire list encoding is preserved and the suffix is processed from $g$.

**Key facts.** `BoolCircuit.CktSatReduction.T_cons`, `BoolCircuit.CktSatReduction.T_ones`.
