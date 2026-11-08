<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairExtractTM_concat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair component concatenation time bound

**Claim.** With both component flags enabled, the extractor computes on each finite bit string the concatenation of the two components when decoding succeeds, and the empty string otherwise, within $5(|z|+1)$ steps.

**Proof.** Fix an input $x$. The component extraction theorem (`pairExtractTM_computes`), with both flags true, gives the claimed output and time bound directly. Unfolding the definition of computing a function, and considering whether decoding returns no pair or a pair, identifies this output with the specified function value. Thus the machine computes that function on every input within the stated time.

**Key facts.** `Turing.FinTM.pairExtractTM_computes`.
