<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairExtractTM_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second component extraction time bound

**Claim.** For every finite bit string $x$, the extractor with only its second-component flag enabled halts within $5(|x|+1)$ steps and outputs the decoded second component when parsing succeeds, and the empty string otherwise.

**Proof.** Fix $x$ and apply the component extraction theorem (`pairExtractTM_computes`) with the first flag false and the second true. If decoding fails, the output is empty. If decoding yields $(a,b)$, the output is the empty string followed by $b$, which equals $b$. This is the specified function value, with the same time bound.

**Key facts.** `Turing.FinTM.pairExtractTM_computes`.
