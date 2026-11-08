<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.actionBitsK_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Delimiter of an Action Encoding

**Claim.** The bit string encoding any action ends in $0$.

**Proof.** The encoding ends with the encoding of the optional successor state. If that state is absent, its encoding is the one-bit word $[0]$. If it is present, its encoding is a leading $1$, followed by the unary encoding of its index; that unary encoding terminates in $0$. Thus in either case the state encoding has the form $v++[0]$. Substituting this final segment into the concatenation defining the action encoding shows that the whole action encoding also has the form $u++[0]$.
