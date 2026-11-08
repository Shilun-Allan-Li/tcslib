<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldCfg_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Origin flag at a folded head

**Claim.** In the folded configuration, the origin flag in the unpacked symbol under tape $i$’s head is true exactly when the folded head coordinate is zero.

**Proof.** The folded head coordinate is nonnegative, so the folded tape stores the packed symbol formed from the original tape’s two reflected cells, together with the flag that records whether the folded coordinate is zero. Unpacking this packed value recovers that symbol unchanged (the unpack-after-pack identity, `foldUnpack_pack`). Its first component is therefore the zero test for the folded head coordinate, as claimed. The nonnegativity needed for the stored tape branch follows from nonnegativity of every folded coordinate (`foldPos_nonneg`).

**Key facts.** `Turing.FinTM.foldPos_nonneg`, `Turing.FinTM.foldUnpack_pack`.
