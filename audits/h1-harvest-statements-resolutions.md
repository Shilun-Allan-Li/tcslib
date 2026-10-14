# H1 hosted-clock harvest statement gate: resolutions (round 1; gate CLOSED)

**Gate:** the public counter loop over the step block, `Build/StepBlockLoop.lean`
(`Turing.StepBlock.loopTM`, `hostedLoopTM`, `loopTM_run`, `hostedLoopTM_run`, `hostedLoop_read`),
with the companion edit to `CodeSimulator.lean` (`audits/h1-harvest-statements-pack.md`; bundle
SHA-256 `1b294f312a89211072a0dcaf42a445c0e2ae10338fe7e798adcfba3ab373a596`, 66 sections, dispatch
folder 20).

**Round 1** (`audits/h1-harvest-statements-findings.md`, verbatim): **PASS, 0 blockers, 0 majors, 4
minors. The gate closes.**
- **C1 ruling 5:** satisfied item by item.
- **R's loop phase:** both time clauses and the branch verdict follow.
- **Adversarial instantiations:** none breaks a public contract. `live` and the tag hypothesis
  are each shown necessary.
- **The companion edit:** applies with zero fuzz and removes exactly the eight disclosed private
  declarations (269 lines).
- **Duplication ledger:** accepted.

The auditor did not run Lean. The elaboration and axiom results stay maintainer evidence, and the
merged-base compile and replay are landing obligations.

## Findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| H1-1 | minor | `decls.py`'s freeze, move-map and reference checks have false passes: an extra import, a changed moved bound and a qualified reference all pass | **Fixed for the landing.** The landing's checks:<br>• assert the permitted outside-declaration delta and the surviving declaration order;<br>• enforce kinds, visibility and unchanged signatures for the move-map entries;<br>• recognize qualified references.<br>Each gets a control that must exit nonzero. Cross-module elaboration stays a separate landing check |
| H1-2 | minor | `runall.sh` §6's three elaborations and the unresolved-name lists do not affect the exit status | **Fixed for the landing.** Each elaboration's status and diagnostics are checked against expectations, and the unresolved-name sets are asserted. The landing notes say exactly which checks gate the exit |
| H1-3 | minor | `neg2` is vacuous: its conclusion has no run equation, so `T = 0` proves it | **Fixed for the landing.** The negative control keeps the run endpoint and first-exit requirement and uses the auditor's large-borrow counterexample (`w = false^(B+2) ++ [true]`, `t = 2^(B+2)`). The old file is relabelled as a failed proof-reuse test |
| H1-4 | minor | `loopTM_run`'s proof sketch (unit line 319; landed module line 283) still cites the deleted `h1Clock_orbit` | **Fixed for the landing:** it cites `loopOrbit_rep` ("formerly `h1Clock_orbit`"). Citations are validated in the landing context alone, not in the union with the overlay |

## Open questions (the auditor recommends the pack's proposals; the user decides)

1. Home `Build/StepBlockLoop.lean`, namespace `Turing.StepBlock`.
2. Registry row H2-L after H2, marked landed only when it lands.
3. The five public names as proposed.
4. Land on the merged base (#92 and #93 merged): a 9-module replay including `SelfUniversal`,
   keeping #92's facade additions.
5. One maintainer landing PR with its replay; no fill brief. R's brief cites the public contracts.
6. A public `Turing.counterValue_bits : counterValue t.bits = t` beside `counterValue`, with a
   small, separately reviewable proof that reuses or moves the word-value bridge.
7. R's sketch (`NDCodeSimulator.lean:117–120`) re-pointed at landing to `hostedLoopTM_run` and
   `hostedLoop_read`, without the stale "private" and "harvested with H2's promotion" wording.
