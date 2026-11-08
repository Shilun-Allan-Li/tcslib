<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairExtractTM_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First component extraction time bound

**Claim.** For every finite bit string $x$, the extractor with only its first-component flag enabled halts within $5(|x|+1)$ steps and outputs the decoded first component when parsing succeeds, and the empty string otherwise.

**Proof.** Fix $x$ and apply the component extraction theorem (`pairExtractTM_computes`) with the first flag true and the second false. If decoding fails, its output expression is empty. If decoding yields $(a,b)$, the output expression reduces to $a$ followed by the empty string, hence to $a$. These are precisely the values of the stated function, and the time bound is already the one asserted by that theorem.

**Key facts.** `Turing.FinTM.pairExtractTM_computes`.
