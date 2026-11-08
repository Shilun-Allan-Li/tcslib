<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.rcode_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability and bounded runs

**Claim.** A code is reachable by encoded steps inside the $s$-window exactly when it is the code of the final configuration of a finite choice string whose every prefix run stays in that window.

**Proof.** Proceed in both directions. For the forward direction, induct on the reflexive-transitive reachability derivation. In the reflexive case, the empty choice string gives the initial configuration, which lies in the window. For a final encoded step, the step-language characterization (`mem_stepLang`) supplies window configurations $C,C'$, their codes, and a choice bit $b$ taking $C$ to $C'$. The induction hypothesis gives a choice string $w$ and identifies its final code with that of $C$. Since both configurations lie in the window, code equality implies equality of their core summaries (`coreSum_eq_of_code_eq`). Applying the same choice bit preserves equality of core summaries (`coreSum_stepWith`), so the run on $w$ followed by $b$ has the same core summary as $C'$. The window property transfers along this equality (`inWindow_of_coreSum_eq`), and the resulting codes agree (`code_eq_of_coreSum_eq`). The prefix-window condition is preserved by appending this final bit (`WinRun.snoc`).

Conversely, take a choice string $w$ with all prefix runs in the window. Induct on the prefix length $j$. Length zero is reflexive reachability. At the successor stage, the next bit gives a valid encoded step: the preceding and succeeding prefix configurations lie in the window, and the run recursion identifies them as related by that bit. Thus every prefix code is reachable, including the code for the full string.

**Key facts.** `Complexity.ExpBFS.inWin_init`, `Complexity.Codec.mem_stepLang`, `Complexity.ExpBFS.WinRun.last`, `Complexity.ExpBFS.coreSum_eq_of_code_eq`, `Turing.NDTM.coreSum_stepWith`, `Turing.NDTM.inWindow_of_coreSum_eq`, `Complexity.ExpBFS.code_eq_of_coreSum_eq`, `Complexity.ExpBFS.WinRun.snoc`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`.
