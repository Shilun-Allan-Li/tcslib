<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_pairFst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-component extraction

**Claim.** A finite Boolean Turing machine computes the first component returned by the aligned pair parser, using the empty word when parsing fails, in time bounded by a constant times $|x|+1$.

**Proof.** Use the pair-extraction machine configured to retain the first component and discard the second. Its computation theorem gives the output selected from a successful parse and the empty word on failure, within $5(|x|+1)$ steps (`pairExtractTM_computes`). To identify this output with the stated function, split according to whether parsing fails or returns a pair; in each case, the selected first component agrees with the parser expression, with the failure case giving the empty word.

**Key facts.** `Turing.FinTM.pairExtractTM_computes`.
