<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.recode_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability under recoding

**Claim.** If $u$ belongs to the $s$-window reachability set, then its recoded value belongs to the $(s+1)$-window reachability set.

**Proof.** Represent $u$ by a choice string $w$ whose every prefix run stays in the $s$-window and whose final configuration has code $u$ (`mem_rset`, `rcode_iff`). The recoding specification (`recode_spec`) identifies the recoded value with the code of that same final configuration in the larger window. Since $s\le s+1$, the run also stays in the larger window by monotonicity (`WinRun.mono`); the reachability characterization and set-membership equivalence therefore put that code in the $(s+1)$-window reachability set.

**Key facts.** `Complexity.ExpBFS.mem_rset`, `Complexity.ExpBFS.rcode_iff`, `Complexity.ExpBFS.recode_spec`, `Complexity.ExpBFS.WinRun.mono`.
