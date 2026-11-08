<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.skipSymbols_consumes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated triple-skip consumption

**Claim.** If every successful read by $r$ consumes at least $b$ symbols, then success after iterating the operation that applies a reader three times, $j$ times, consumes at least $b3^j$ symbols.

**Proof.** We induct on $j$, allowing the input and output strings to vary. For $j=0$, the iterated reader is the identity, and the assumed consumption bound for $r$ gives the result. At the successor stage, the iteration definition expresses the reader as three successive applications of the reader from stage $j$. By induction, each successful application of that stage consumes at least $b3^j$ symbols. The repeated-reader consumption bound (`skipRepeat_consumes`) therefore gives a total of at least $(b3^j)3=b3^{j+1}$ symbols, as required.

**Key facts.** `Turing.MachineFormat.skipRepeat_consumes`.
