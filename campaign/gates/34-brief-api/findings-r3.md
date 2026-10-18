External audit of PR #118, round 3 — the brief-inventory API

Audited the supplied packet with one agent and no sub-agents. The bundle's SHA-256 is `2b75b76570c90aa735eeff2ef8297d024354d48f518e545843ba828eac6a6c9a`, exactly the commissioned value. All 124 section paths are unique. Source line numbers below exclude the bundle's enclosing code fences. The source comparison is round 2's `4624fc05` to the supplied round-3 files at `531b98a2`.

Round 2's major is closed. All eight added equations are faithful, and I found no further missing primitive equation on the supplied routes. Two minor record corrections remain.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `audits/evidence/brief-api/r3/unfold-sites-r3.tsv`; its `review-out/` and `drafts/mig12-fill/unfold-sites.tsv` copies | Three entries in the binding replacement ledger still give the pre-repair interfaces, omitting the two laws added specifically for those entries. | The `counterWord` entry for `CfgRecord:529` says `counterWord_zero/_length/_value`, omitting `counterWord_succ`. Both entries for `CfgRecord:1189` still say `scanResult_fold (no own lemma)` or `scanResult_* (no own lemma)`, omitting `scanResult_keep_keep`. The three ledger copies are byte-identical. The draft's Phase 4 table correctly names the new laws, so this is a disagreement within the records, not a remaining API gap. | Update the line-529 entry to cite `counterWord_succ` and `counterWord_zero`; update both line-1189 entries to cite `scanResult_keep_keep` as the replacement for the identity-scan argument. Synchronize all three copies. |
| 2 | minor | `audits/evidence/drafts/mig12-fill-cfgrecord.DRAFT.md`, `b6-fill-rulerdevice.DRAFT.md`, and `drafts/README.md` · import-probe descriptions | The draft descriptions do not distinguish their historical probe counts from the enlarged round-3 probes. | MIG-12 still describes its probe as 219 checks; the supplied probe source has 227 distinct `#check`s and its round-3 output prints 227 names. F5's draft and the README still say 52; its round-3 output prints 58 distinct names. The pack and resolutions correctly state 227 and 58 and identify the round-3 snapshot. | Describe the current probes as MIG-12 227 and F5 58, against `oleans-lbapi4`. Retain 219/52 and the earlier snapshots only where explicitly labeled as historical measurements. |

Answers to the pack's five questions:

| Question | Result | Evidence and limits |
|---|---|---|
| 1. Round 2's findings | Major closed; omitted sites and erratum repaired; minor record residue above | The four `Action.apply` equations give precisely its non-tape fields. `step_of_some` and `outputSymbol_of_some` give the previously missing live cases for arbitrary machines. The ledger now includes all previously reported multiline and orbit entries, and correctly records one direct `counterLoopTM_run_escape` use at `CfgRecord:895`. The resolutions correctly record 12 MIG-12 names and 33 total names for round 2. |
| 2. Other primitive readings | No additional gap identified on the stated routes | The step and emission have both live and halted cases; all five applied-action fields are covered, including the existing `Action.apply_workTapes`; initialization has `initCfg_eq` and the `Cfg.init_*` equations; runs have zero, successor and addition equations. Head motion and scanned symbols have complete case/field interfaces. See the scope qualifications below. |
| 3. The two private-only laws | Faithful and appropriately located | `counterWord_succ` is beside `counterWord` and its zero law. It describes the frozen optional-decrement orbit, including underflow. `scanResult_keep_keep` is beside `scanResult_fold` in the scan-instance group and preserves both the state and the word for arbitrary types and words. |
| 4. No behavior change | Satisfied for both supplied patches | Both patches reverse cleanly against the supplied sources, and every before/after Git blob hash matches its patch. The changes total 69 additions and three deletions. All three deleted lines are module documentation. The additions are documentation, four handwritten theorems and the attribute generating four field equations. Existing definitions, statements, proof bodies, imports and admissions are unchanged. No new equation is registered as a simp lemma. |
| 5. Duplication and records | No new substantive duplication identified; two record corrections above | The supplied 14-file screens retain exactly the same 487 pair rows and 139,742 reproduced characters. An independent comparison of all affected screened bodies against the seven supplied Lean files finds no new pair. Replay, warning and name-count records agree with their supplied outputs as detailed below. |

The corrected ledger contains 173 distinct entries: 76 explicit `(line, definition)` pairs at 69 lines, and 97 implicit pairs at 81 lines in 30 declarations. Every entry's source text matches its source line. Re-running the supplied multiline scanner reproduces its 76-row output byte for byte; 44 entries are marked as inherited from the round-2 ledger.

The 34 individual-definition logs contain 104 errors at 99 distinct `(line, definition)` pairs, after accounting for their four inserted lines. Exactly two pairs already occur in the explicit ledger; the other 97 are exactly the implicit ledger. All 80 broad-run errors, at 75 distinct source lines, have a corresponding individual-definition failure site. The broad candidate list has 200 definitions, as claimed.

This establishes agreement between the ledger, source and supplied detection outputs. It does **not** establish an exhaustive inventory of every implicit reduction: a failing tactic can conceal later reductions, and reducible abbreviations are outside the stated irreducibility experiment. Those limitations are acknowledged in the pack and draft. The ledger's opening phrase “every site” should be read with those qualifications; the 97 entries are detected uses, not a completeness theorem. No additional missing API follows merely from this methodological limitation.

For primitive coverage, the new statements expose exactly the following formulas, with the parameters and types of the supplied declarations:

```lean
(a.apply c).state = a.state
(a.apply c).inputPos = moveInputPos c.inputPos a.inputTape
(a.apply c).workTapePos i = c.workTapePos i + ((a.workTapes i).2 : ℤ)
(a.apply c).output = c.output ++ a.output.toList

c.state = some q →
  M.step c = (M.tr q c.inputSymbol c.workTapeSymbols).apply c
c.state = some q →
  M.outputSymbol c = (M.tr q c.inputSymbol c.workTapeSymbols).output
```

`Action.apply_workTapes` supplies the remaining field through a point update at the old head, and `Cfg.workTapeSymbols_eq` identifies the old scanned cell. Together these cover the arbitrary-action uses in `recordStep_window`, `recordStep_tape_word`, `recordStep_position_run` and `recordStep_apply_run`. The live equations directly replace the unfoldings in `recordStep_observed_action`. They also suffice to expose F5's arbitrary source transition: its source control, clamped input movement, bank writes and head movements, and emission. No specialized leaf hypothesis is present.

The run equations cover time zero and every successor. Combining them with the two cases of `step` permits induction on runs without unfolding `runFrom`. Likewise, `initCfg_eq` followed by the five `Cfg.init_*` equations exposes every initial field. The input-reading cases cover the left blank, right blank and interior; the movement cases cover all three directions at both boundaries and in the interior.

Neither supplied `CfgRecord` nor `InputDevice` contains a use of `spaceUsed` or `spaceUsedByTape`. F5's formal space clauses are visited-set equality and inclusion; `mem_visitedByTapeHead_iff` and the split/run lemmas address those clauses directly. Thus no definitional space equation is needed for these two routes. For U2-S, the supplied review names the existing space-bound lemmas, and the name inventory confirms they are public. F3, G4 and continuation 6 retain the route dispositions accepted in round 2. Their complete current source/draft sets are not included in this packet; I checked the supplied review and scans, rather than claiming a fresh full-source audit of those briefs. The deferred general-alphabet counter-loop layout issue remains outside the stated primary routes.

Restatements of the definitions whose behavior the equations expose:

| Definition | Mathematical content |
|---|---|
| `Action.apply` | Set the next state to the action's optional state; clamp the input-head move; optionally write each work tape at its old head, then move that head by its signed displacement; append the optional emitted symbol to the existing output. An outer `none` means no write, while `some none` erases the old head cell. Applying an action itself requires no live-state hypothesis. |
| `MultiTapeTM.step` | Leave a halted configuration unchanged. At a live state, choose the transition from the current input/work symbols and apply it to the current configuration. |
| `MultiTapeTM.outputSymbol` | Return `none` at a halted configuration; otherwise return the optional output of the transition selected from the current readings. A transition that enters the halted state may still emit a symbol. |
| `Cfg.init`, `MultiTapeTM.initCfg` | Start in `some q₀`, with input position 1, blank work tapes, all work heads at 0 and empty output. A machine's initializer uses its own start state. |
| `MultiTapeTM.runFrom` | Iterate the step operation the specified natural number of times, including zero applications. A halted configuration therefore remains fixed. |
| `counterWord` | Iterate optional fixed-width decrement, retaining the previous word whenever decrement returns `none`. This freezes at zero; it does not model the physical counter's underflow wrap. |
| `scanKeep`, `scanFold` | The first preserves the state and current symbol. The second updates the state by its supplied function while preserving the symbol. |
| `scanResult` | Run the forward transducer over the word, then the backward transducer over the reversed rewritten word, starting from the forward pass's final state. Reverse the backward output to restore word order. |

These restatements agree with the relevant docstrings. There are no new definitions or admitted theorems in this round.

Adversarial checks below are deductions from the supplied definitions/equations, not claimed Lean executions:

1. **Empty input, zero work tapes and boundary moves.** Empty input still has the two positions 0 and 1. The movement laws give `moveInputPos 0 (-1) = 0` and `moveInputPos 1 1 = 1`, so the input equation does not wrap at either boundary. With zero work tapes, only the tape-indexed equations are vacuous; state, input and output equations remain meaningful. No positivity or finiteness hypothesis is missing.
2. **A halting transition that emits.** If `c.state = some q` and the chosen action has state `none` and output `some b`, the live-step and action-field equations give `(M.step c).state = none` and `(M.step c).output = c.output ++ [b]`. The subsequent halted-step equation keeps that configuration fixed, and its emission is `none`. Thus the repair neither drops the last emitted symbol nor repeats it after halting.
3. **Counter underflow and a padded word.** The successor and zero laws give `counterWord [] 1 = (decFixed []).getD [] = []`. For the little-endian word `[false, true]`, successive words are `[true, false]`, then `[false, false]`, then `[false, false]` again: the first two decrements succeed, while the third returns `none` and `getD` retains zero. The law therefore needs no bound on the decrement count and does not accidentally assert wraparound.
4. **Identity scan, including the empty word.** Induction on the word gives `mealyRun scanKeep a₀ w = (a₀, w)`: the empty case returns its inputs; the successor case preserves the current symbol/state and applies the induction hypothesis to the tail. Substitution into `scanResult` gives `(a₀, w.reverse.reverse) = (a₀, w)`. This verifies both components, without a nonempty-word or finite-type assumption.

Verification records and practical limits:

- Both committed patches have the same source changes as their corresponding review patches. The matched final blob prefixes are Configuration `a9f14a78`, Deterministic `efd291b1`, CounterLoop `963a97ec`, and Catalog `c2802df7`; these agree with the replay script's pins.
- The eight printed types match the source formulas. Their supplied axiom outputs contain only `propext` and, except for the identity scan, `Quot.sound`. The review probes print `simp=false` for all eight. The supplied consumer/control outputs are consistent with the review's account; the rewritten CfgRecord consumer sources themselves are not included, so those executions remain attestations.
- The four-file lint independently returns zero FAIL before and after, with the same four WARN records apart from file sizes. Check 8's uncovered-name lists are unchanged. The full supplied logs agree on zero FAIL and 67 WARN over 79 files; the full tree is not supplied for independently repeating that run.
- The recorded warning-message multisets agree before and after: Configuration 3, Deterministic 0, CounterLoop 0, Catalog 77. The replay lists 320 distinct modules in exactly the supplied order, all with exit/error counts zero, and 94 sorry warnings in total. Its static-comparison output reports zero mismatches and total 94. The two round-3 draft outputs contain 58 and 227 distinct checks and no error lines.
- The supplied wide-screen pair rows are byte-identical. For the independent seven-file comparison, the screen extracts 662 then 663 declarations. Only `Action.apply`'s extracted body (which includes its new attribute) and the new `scanResult_keep_keep` body differ; comparing every pair involving either body produces no qualifying pair before or after. Unchanged-body pairs cannot change under this screen. This is an incremental reproduction of the change, not a rerun of the unavailable full 14-file population.
- The public `counterWord_succ` and retained private `counter_word_succ` have the same statement and one-line application of `Function.iterate_succ_apply'`. The screen excludes these short bodies. This disclosed export duplication is not a new wholesale proof copy; the review explicitly leaves consolidation to the later body-edit window. The new identity-scan law is distinct from the existing private, general `scanResult_keep`.

Lean and Lake are unavailable in this environment. Elaboration, axiom printing, consumer execution and downstream compilation were therefore checked as supplied execution evidence, not independently rerun. No external repository was accessed or modified. The packet supports the source and record checks above, but does not independently certify Git ancestry or fresh-olean provenance.

Notation: all code identifiers and parameters retain their meanings in the supplied Lean files; no additional mathematical notation is introduced.

PASS — 0 blockers, 0 majors, 2 minors, 0 notes.
