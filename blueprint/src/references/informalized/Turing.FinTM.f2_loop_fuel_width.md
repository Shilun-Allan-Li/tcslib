<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_fuel_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit-string Output Length Bound

**Claim.** If $F$ halts within $T(|y|)$ steps on every input $y$ and outputs the binary expansion of $R(|y|)$, then for every Boolean word $x$ the length of that binary expansion is at most $T(|x|)$.

**Proof.** Apply the computation hypothesis to $x$. It supplies a space witness together with the fact that the output after $T(|x|)$ steps is the binary expansion of $R(|x|)$. A machine's output length after $t$ steps is at most $t$ (`Turing.MultiTapeTM.output_length_le`), since each step can append at most one output symbol. Substituting the specified output gives the claimed bound.

**Key facts.** `Turing.MultiTapeTM.output_length_le`.
