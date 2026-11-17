<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.scan_full -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan Returns the Parsed Remainder

**Claim.** For every bit string $x$, scanning $x$ returns exactly the remainder obtained by parsing $x$, when parsing succeeds; if parsing fails, scanning also fails.

**Proof.** After the common pair decoding and the two common validity checks, compare the remaining computations. Parsing reads the initial state as a finite-state value, while scanning skips that same unary code. Erasing the value from a successful finite-state read leaves exactly the result of skipping it (`codeEraseFin`). The two procedures then process the table: parsing reads it and scanning skips it, and the table format's erasure property identifies the remainder from the table read with the result of table skipping. This correspondence is preserved when each operation is sequenced after the preceding one (`codeErase_bind`). Both procedures finally apply the same test that the remaining suffix consists entirely of $1$s. When that test passes, parsing returns the assembled code together with the suffix, and mapping to the second component returns that suffix; when it fails, both results are failure. Thus the scan result equals the parsed remainder whenever parsing succeeds, and both are failure otherwise.

**Key facts.** `Turing.codeEraseFin`, `Turing.codeErase_bind`.
