<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.outSummary_eq_empty_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterisation of the empty summary

**Claim.** A finite Boolean string has the empty output summary if and only if it is empty.

**Proof.** Split into the empty string and a nonempty string. The empty string has empty summary. For a nonempty string, separate its first bit and distinguish whether any bits remain. A one-bit string has accepting summary when its bit is $1$ and dead summary when its bit is $0$; strings with at least two bits have dead summary. Hence no nonempty string has empty summary.
