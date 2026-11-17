<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.outSummary_eq_accept_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterisation of the accepting summary

**Claim.** A finite Boolean string has the accepting output summary if and only if it is exactly the one-bit string $[1]$.

**Proof.** Split into the empty string and a nonempty string. The empty string has empty summary, so it is not accepting. For a nonempty string, separate its first bit and then distinguish whether the remaining string is empty. The only case with accepting summary is first bit $1$ and no remaining bits, which is precisely $[1]$; all other cases have dead summary. Thus the summary is accepting exactly for $[1]$.
