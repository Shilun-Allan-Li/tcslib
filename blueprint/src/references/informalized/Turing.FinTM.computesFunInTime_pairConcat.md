<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_pairConcat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Parsed Pair Components

**Claim.** A finite Turing machine outputs the concatenation of the two components returned by the aligned pair parser when parsing succeeds, and the empty word when it fails, in linear time.

**Proof.** Choose `pairExtractTM` with both component-selection flags set to true, and take $c=5$. Its computation theorem `pairExtractTM_computes` gives the output formed from both parsed components, or the empty word on failure, in $5(|z|+1)$ steps. Split on whether parsing fails or returns a pair; in either case, selecting both components makes that output exactly the specified concatenation (or empty word).

**Key facts.** `Turing.FinTM.pairExtractTM_computes`.
