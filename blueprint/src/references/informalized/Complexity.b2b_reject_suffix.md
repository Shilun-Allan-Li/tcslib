<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_reject_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejecting Round Suffix

**Claim.** When the incremented word $v$ has the same length as $u$, the round body clears the suffix data, increments its first tape, and reaches the test anchor with first tape $v$ and all other tapes blank. It does so at a positive time, avoids both specified test states at all earlier times, and keeps all work-head positions within the stated bound.

**Proof.** Write $y=x	exttt{++}u$. First run the clear phase for $C=2|y|+2$ steps. The clearing-run theorem (`Turing.clearTM_run_ofCfg`) shows that this phase reaches its done state, erases the second tape, and bounds every head during the pass. The phase-host run theorem (`Turing.phaseHostTM_run`) carries this run into the body machine and redirects its done state to the increment phase. Next run the increment phase for $I=2|u.	exttt{takeWhile id}|+2$ steps. The increment-run theorem (`Turing.incrementTM_run_succ_ofCfg`), using the hypothesis that the fixed-width increment of $u$ is $v$, shows that the first tape now stores $v$ and the phase reaches its true done state. Since the redirect is defined there, the phase-host theorem adds one transition to return to the test anchor. Thus take $T=(C+1)+(I+1)$, which is positive. Before the endpoint, every time is covered by either the clearing segment or the increment segment; their run bounds exclude both the test anchor and the true-verdict state. The same coverage transfers the respective head bounds to the body run. In the clearing segment, heads are bounded by the scanned length $|y|=|x|+|u|$; in the increment segment, they are bounded by the scanned length $|u|$; these imply the claimed bound $|x|+|u|+1$. At the endpoint all heads are zero, so the bound holds there as well. The decomposition of the run at the phase boundary uses the run-addition identity (`Turing.MultiTapeTM.runFrom_add`).

**Key facts.** `Turing.clearTM_run_ofCfg`, `Turing.incrementTM_run_succ_ofCfg`, `Turing.phaseHostTM_run`, `Turing.MultiTapeTM.runFrom_add`.
