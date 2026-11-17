<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.emRun_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate-List Emission

**Claim.** Reading an encoded finite list of gates, each with at most two arguments, from gate phase at counter $z$ emits the serialized concatenation of their successive Tseitin formulas, followed by a false bit.

**Proof.** Induct on the gate list, generalizing the starting counter $z$. For the empty list, the list encoding is its false terminator, which the gate phase emits as the final false bit. For a nonempty list, write its first gate as $(k,\mathrm{args})$. The initial true bit and the two bits encoding the gate kind move the machine from gate phase to argument-reading phase for kind $k$, without changing the remaining input. The argument-reading result ($\texttt{emRun\_args}$) then emits the serialized Tseitin formula for this gate at index $z$ and resumes in gate phase at index $z+1$. The induction hypothesis applies to the remaining encoded gates, since each still has at most two arguments, and emits their formulas followed by the terminator. Concatenating these outputs gives exactly the serialization associated with the recursively concatenated Tseitin formulas.

**Key facts.** `BoolCircuit.CktSatReduction.Emitter.emRun_args`.
