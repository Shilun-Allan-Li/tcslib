<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.winRun_of_card_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal counts preserve bounded runs

**Claim.** If the reachable-code sets for windows $s$ and $s+1$ have equal cardinality, then every finite choice string has all its prefix configurations in the $s$-window.

**Proof.** Induct on the choice string by removing its last bit. The empty string has only the initial configuration, which lies in the window (`inWin_init`). Suppose the result holds for $w$, and append a bit $b$. The last configuration after the appended bit lies in the $(s+1)$-window: the previous endpoint is in the $s$-window by the induction hypothesis (`WinRun.last`), and one transition enlarges the window bound by at most one (`inWin_stepWith`), using the run concatenation identities.

The extended run stays in the $(s+1)$-window, by monotonicity and the endpoint just established (`WinRun.mono`, `WinRun.snoc`). Its final code therefore belongs to the larger reachable set (`rcode_iff`, `mem_rset`). Equal cardinalities make that set the image of the smaller reachable set under recoding (`image_recode_of_card_eq`). Hence this final code is the recoding of some $s$-reachable code. Represent that code by a run $w'$ (`mem_rset`, `rcode_iff`) and use the recoding specification (`recode_spec`) to identify the two $(s+1)$-window codes. The corresponding core summaries are equal (`coreSum_eq_of_code_eq`); transferring the window property back along this equality (`inWindow_of_coreSum_eq`) shows that the extended run's endpoint is already in the $s$-window. Together with the induction hypothesis, this gives the required prefix condition for $w$ followed by $b$ (`WinRun.snoc`).

**Key facts.** `Complexity.ExpBFS.inWin_init`, `Complexity.ExpBFS.WinRun.last`, `Complexity.ExpBFS.inWin_stepWith`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`, `Complexity.ExpBFS.WinRun.mono`, `Complexity.ExpBFS.WinRun.snoc`, `Complexity.ExpBFS.rcode_iff`, `Complexity.ExpBFS.mem_rset`, `Complexity.ExpBFS.image_recode_of_card_eq`, `Complexity.ExpBFS.recode_spec`, `Complexity.ExpBFS.coreSum_eq_of_code_eq`, `Turing.NDTM.inWindow_of_coreSum_eq`.
