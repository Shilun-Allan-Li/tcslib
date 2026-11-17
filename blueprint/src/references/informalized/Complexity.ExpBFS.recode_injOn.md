<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.recode_injOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the recoding map

**Claim.** On the $s$-window reachability set, equal recoded values imply that the original reachable codes are equal.

**Proof.** Take two elements of the reachability set with equal recodings. By membership in the reachable set and the reachability characterization (`mem_rset`, `rcode_iff`), represent each code by a choice string and its run configuration. The definition of recoding agrees with the $(s+1)$-window code of that run (`recode_spec`), so the assumed equality is equality of those larger-window codes. Each run stays in the larger window by monotonicity (`WinRun.mono`), hence its final configuration lies there (`WinRun.last`). The code-equality-to-core-summary principle (`coreSum_eq_of_code_eq`) now identifies the two core summaries; the converse principle (`code_eq_of_coreSum_eq`) then gives equality of their original $s$-window codes.

**Key facts.** `Complexity.ExpBFS.mem_rset`, `Complexity.ExpBFS.rcode_iff`, `Complexity.ExpBFS.recode_spec`, `Complexity.ExpBFS.WinRun.mono`, `Complexity.ExpBFS.WinRun.last`, `Complexity.ExpBFS.coreSum_eq_of_code_eq`, `Complexity.ExpBFS.code_eq_of_coreSum_eq`.
