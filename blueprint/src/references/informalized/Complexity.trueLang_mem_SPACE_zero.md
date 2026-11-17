<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.trueLang_mem_SPACE_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Language Uses Zero Space

**Claim.** The language of all finite binary words belongs to $\mathrm{SPACE}(s)$ for the identically zero bound: a finite machine decides it while using at most zero work-tape cells on every input.

**Proof.** Choose the space constant to be zero and use the machine that always outputs true. Its work-tape count is zero, so the zero-space principle for machines with no work tapes guarantees space usage zero whenever the machine computes the required output (\texttt{computesInSpace\_zero\_of\_k\_eq\_zero}). On each input, the constant-true machine computes the one-symbol output $[\mathrm{true}]$ in one step (\texttt{constTrueTM\_computesInTime}). This is exactly the indicator output for the universal language. Hence it decides that language within the stated zero-space bound.

**Key facts.** `Turing.FinTM.computesInSpace_zero_of_k_eq_zero`, `Complexity.constTrueTM_computesInTime`.
