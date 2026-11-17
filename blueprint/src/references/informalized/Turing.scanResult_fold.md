<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.scanResult_fold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fold Scan Output

**Claim.** The two-pass fold scan returns the left fold of δ over the word, together with the unchanged word.

**Proof.** A second keep scan does not alter the result of the first pass (`Turing.scanResult_keep`). For that first pass, use induction on the run of the transducer, proving that scanning any word l from state b returns the pair consisting of the fold of δ over l from b and l itself. The empty word gives (b, []). For a head γ followed by l, the first transition changes the state to δ b γ and leaves γ in place. Apply the induction hypothesis to the tail from the new state: its result is the fold over l starting at δ b γ, paired with l. The recursive definition of left fold identifies this state with the fold over γ :: l from b, while the output symbols form γ :: l.

**Key facts.** `Turing.scanResult_keep`, `Turing.mealyRun_induction`.
