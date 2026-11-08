<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.scanResult_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Map Scan Output

**Claim.** The two-pass map scan returns the unchanged state a₀ and the word obtained by applying f to every symbol.

**Proof.** The second keep scan leaves the first pass unchanged (`Turing.scanResult_keep`). For the first pass, induct on the transducer run, maintaining that a scan of l from any state b returns (b, map f l). The empty word satisfies this directly. On a head γ followed by l, the map transition leaves b fixed and outputs f γ; the induction hypothesis gives map f l on the tail, so the output is f γ followed by map f l, namely map f (γ :: l) (`Turing.mealyRun_induction`).

**Key facts.** `Turing.scanResult_keep`, `Turing.mealyRun_induction`.
