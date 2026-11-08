<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadSymbols_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol-row decoding

**Claim.** If a value reader correctly reads each encoded value followed by a suffix, then the three-entry symbol-row reader correctly reads the row encoded from $f$ and leaves the given suffix unchanged.

**Proof.** The row serialization concatenates the encodings of the values of $f$ at blank, $0$, and $1$, followed by $x$. Associativity of concatenation lets us apply the assumed prefix-inverse property successively: the first read returns the blank entry and leaves the encodings of the other two entries followed by $x$; the second returns the $0$ entry and leaves the final entry followed by $x$; and the third returns the $1$ entry and leaves $x$. The row reader assembles these three values into the function that agrees with $f$ at each of its three possible inputs, so its returned function is $f$, and its suffix is $x$.
