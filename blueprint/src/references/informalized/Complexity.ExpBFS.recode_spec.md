<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.recode_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of recoding

**Claim.** For any choice string whose prefix runs stay in the $s$-window, recoding the code of its final configuration gives the code of that same configuration in the $(s+1)$-window.

**Proof.** The reachability characterization (`rcode_iff`) first shows that the given final code is reachable, with the supplied choice string as a witness. Thus the recoding map selects some witness string for that code. The characterization says this selected string reaches the same $s$-window code as the supplied string. Both final configurations lie in the $s$-window (`WinRun.last`), so equality of their codes forces equality of their core summaries (`coreSum_eq_of_code_eq`). Equal core summaries give equal configuration codes at any window size (`code_eq_of_coreSum_eq`); in particular their $(s+1)$-window codes agree, yielding the claimed recoding identity.

**Key facts.** `Complexity.ExpBFS.rcode_iff`, `Complexity.ExpBFS.WinRun.last`, `Complexity.ExpBFS.coreSum_eq_of_code_eq`, `Complexity.ExpBFS.code_eq_of_coreSum_eq`.
