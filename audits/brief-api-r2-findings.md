External audit of PR #118, round 2 — the brief-inventory API

Audited the supplied bundle as a self-contained packet, with one agent and no sub-agents. Its SHA-256 is `901e1fa94e568749c0ad99e1299b9399c0d2e602803a5bbb331cc0b6a7b8c2bd`, exactly the commissioned value. All 108 section paths are unique. Source line numbers below refer to the extracted files, excluding the bundle's enclosing code fences.

Round 1's three findings and the renaming gap N1 are closed. All new equations examined are faithful. The remaining major concerns MIG-12's promised no-unfolding route, not the truth of an added Lean statement.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `Build/CfgRecord.lean` · `recordStep_window`, `recordStep_observed_action`; MIG-12 draft · pre-ship inventory and ground rule 10 | The inventory treats model primitives as covered without establishing the API for the generic action/source-machine readings that MIG-12 must preserve. These uses fall outside the local-leaf exception. | `recordStep_window` (576–599) accepts an arbitrary action. Its head argument identifies `(a.apply c).workTapePos i` with `c.workTapePos i + ((a.workTapes i).2 : ℤ)` by definitional reduction; line 598 also explicitly unfolds `Action.apply`. The field report `seedinv2-G4.out` flags `Action.apply`'s `workTapePos` equation as missing. `Action.apply_workTapes` covers cells, and the head-displacement bound is not the required exact head equation. `recordStep_observed_action` (3314–3339) takes an arbitrary source `M`; lines 3335 and 3337 unfold `MultiTapeTM.step` and `outputSymbol` at a live state. The supplied theorem inventory lists no documented live-state case equation for either. The draft permits unfolding `step`/`Action.apply` only for a leaf defined in the owned file; an arbitrary action or source machine does not qualify. | Publish and probe the exact action-head and live-state equations below, or supply a concrete replacement of these two helper arguments using only already-published lemmas. Inventory these primitive readings rather than excluding them categorically. If compiler-generated equations are intended as the interface, explicitly identify, validate, and document that exception to the publication rule. |
| 2 | minor | `audits/evidence/drafts/mig12-fill/unfold-sites.tsv`; MIG-12 draft · Phase 4 | The claimed 44-site ledger is not exhaustive, even within categories it already counts. | All 44 listed entries match their source lines, but it omits `fieldOffset` at line 2180 and `FinTM.bufferTape` at 2454, 2601, and 2954. Each occurs in a multiline `simpa only [...]` or `simp only [...]` list. Thus there are at least 48 entries under the ledger's existing categories. It also omits the explicit orbit unfoldings at 747 and 760. These omitted names already have suitable interfaces; this is an inventory/accounting defect rather than an additional missing-equation major. | Rescan complete tactic lists across line breaks; include the orbit uses and distinguish abbreviations and primitives explicitly. Update the count and Phase 4 mapping. Use `fieldOffset`'s cases, `bufferTape_nat`/`bufferTape_left`, and the published round-orbit equations. |
| 3 | minor | `audits/brief-api-r2-pack.md` · elaboration attestation | MIG-12 adds 12 API names, not 13. | The patch and probe outputs give four `Action.liftSymbols` fields, three `Cfg.liftSymbols` fields, four increment lemmas, and one decrement lemma: `4 + 3 + 4 + 1 = 12`. The other two commits add 21 names, so this round adds 33 altogether. The pre-existing lift state/head equations are not new additions. | Record the pack erratum in the resolutions: 12 MIG-12 names, 21 other round-2 names, 33 total. |

The interface obligations in finding 1 can be stated as follows, with the parameters and types inherited from the bundled declarations. These are proposed statements, not declarations compiled in this audit:

```lean
(a.apply c).workTapePos i =
  c.workTapePos i + ((a.workTapes i).2 : ℤ)

c.state = some q →
  M.step c = (M.tr q c.inputSymbol c.workTapeSymbols).apply c

c.state = some q →
  M.outputSymbol c = (M.tr q c.inputSymbol c.workTapeSymbols).output
```

The first obligation is used in both directions of the window characterization: a bound on displacement alone does not identify whether an outward move crosses the window boundary. The next two connect the collected record observations to the arbitrary source machine's step and emitted symbol. `catalog_trace_run` does not supply the missing transition equation: its printed statement already assumes the individual `step` equations. Likewise, the specialized `step_of_inputMoveAction` and tape-action lemmas do not cover an arbitrary multitape transition. This is a concrete missing-interface finding, not a claim that the desired facts are mathematically false or impossible to derive by some longer route.

Answers to the six questions:

| Question | Result | Evidence and limits |
|---|---|---|
| 1. Round 1's findings | Closed | `codeSkipRepeat_zero` and `_succ` are exactly the two defining cases. The ten counter-loop field equations expose the arguments passed to `Contract.ofSegment`. `NOTES.md` now correctly says 11 handwritten theorems in the first commit. |
| 2. N1 and the renaming citations | Closed | All nine equations preserve the non-state fields and map only the optional state. Seam/phase-host endpoints do contain `Cfg.mapState`; the U2-S and F5 drafts now cite `Cfg.mapState_state` and its siblings. Their printed import probes include all nine names. The private `Turing.Contract.mapState_state` is a different declaration and remains unchanged. |
| 3. MIG-12 faithfulness and completeness | Equations faithful; completeness not established | The seven lift fields, three increment cases, and two width lemmas agree with their sources. The 68 external-definition rows and 44 recorded unfolding entries are reproducible, but findings 1–2 invalidate the blanket coverage/exhaustiveness claim. The counter-loop use in `CfgRecord` is the Bool loop followed by symbol lifting, so N2's rich-alphabet layout gap is not the obstruction here. |
| 4. Seed-inclusive method and five briefs | Method repaired; route judgments remain necessary | The command inserts each definition seed itself before inspecting its type, and reports missing named fields. Its five outputs have exactly the seed/type unions shown below. The repaired C6 and renaming gaps are visible in those reports. No additional omission was identified among the five briefs' explicitly inventoried primary-route definitions beyond the primitive-read issue that MIG-12 makes concrete. N2 may remain conditional; N3 needs no mandatory repair. The reports are a search aid, not a proof that every future proof step uses an adequate interface. |
| 5. No behavior change | Satisfied for the supplied patches | Reversed all three patches against the supplied sources, verifying every before/after Git blob-hash prefix. Their changes are 56 additions, then 24 additions/one documentation-line deletion, then 12 additions. They add seven handwritten theorems and 26 generated equations, documentation and `simps` attributes; no existing definition, theorem statement, import, or admission changes. |
| 6. Duplication and records | No new duplication found; record corrections above | The two-file duplication screen was independently reproduced before and after, byte for byte. The wider supplied screen retains the same pairs. Replay arithmetic and order lists match. Findings 2–3 correct inventory/count records; execution claims remain supplied evidence, as explained below. |

The method now inventories seeds. Its field test is still syntactic: it checks a directly visible structure result and whether an expected name exists. Whole-value equations, case equations, selected-tape lemmas and machine run/contract interfaces require manual disposition; conversely, merely finding a similarly named theorem is not a semantic coverage proof.

| Brief | Definition seeds | Definitions in cited types | Union | Seeds absent from cited types |
|---|---:|---:|---:|---:|
| U2-S | 22 | 50 | 52 | 2 |
| F3 | 22 | 42 | 44 | 2 |
| F5 | 15 | 23 | 25 | 2 |
| C6 | 49 | 83 | 93 | 10 |
| G4 | 72 | 99 | 101 | 2 |

The substantive exclusions remain justified for the stated routes: the startup uses `cleanTM_run` and keeps the serialized table opaque; F5 owns its ruler encoding and uses the virtual-input host as a model; F3's primary route composes the existing window runner and record-layout lemmas; C6 consumes its already-proved record recognizer rather than re-reading the excluded field skippers and StepBlock implementation; G4 uses the published zone cases, scan-result interfaces, contract fields, and segment/round characterizations.

N2 is a real deferred API need: general-alphabet `counterLoopCfg` has no published layout equation, while `counter_cfg_eq` is Bool-specific. F3's updated draft explicitly requires escalation before activating Route B. C6 and the relevant MIG-12 counter-loop proof use Bool, so neither requires fixing N2 for its present route. N3 is an abbreviation/rewrite usability issue: the supplied consumer probe uses `exact roundOrbit_succ ...` and `simp only [roundOrbit_succ]`, and the C6 draft records this. No new lemma is necessary for that use.

Restatements of the definitions whose API this round extends:

| Definition | Content exposed by the equations |
|---|---|
| `codeSkipRepeat` | Zero repetitions return the input unchanged. A successor first runs the skipper, then repeats on the resulting suffix; failure propagates through `Option.bind`. |
| `Action.mapState` | Map the optional next state through the supplied function; preserve the input move, every work-tape action, and the optional emission. No injectivity assumption is needed. |
| `Cfg.mapState` | Map the optional control state; preserve the input position, all cells, all heads, and output. |
| `Action.liftSymbols` | Preserve the input move, next state and work-head moves. Map the optional emission and both nested optional levels of each write by the embedding. This preserves the distinction between no write and writing a blank. |
| `Cfg.liftSymbols` | Map the input word, occupied work cells and output symbols by the embedding. Recast the input position along the equality of input lengths; preserve the control state and work heads. The new input-position equation correctly contains `Fin.cast`. |
| `incFixed` | Fixed-width little-endian increment: the empty word overflows; a low false bit absorbs the carry; a low true bit becomes false and passes the carry to the tail. A successful increment preserves length. |
| `decFixed` | Fixed-width little-endian decrement: the empty word underflows; a low true bit becomes false; a low false bit becomes true and borrows from the tail. A successful decrement preserves length. |
| `RoundContract.counterLoopDone` | Its precondition supplies the counter's delimited layout and admissible returning body rounds up to its value. Time is the sum of those body times plus the decrements through the final underflow. The post is at `done`, with the final body orbit, all-true counter interval, unchanged counter exterior, and restored counter head. The bounds combine the body-round hull with the counter interval. |
| `RoundContract.counterLoopEscape` | Its precondition chooses an escaping round strictly below the counter value, admits all rounds through it, and requires the earlier rounds to return. Time counts the body rounds and decrements through that escape, without an additional underflow. The post is at `escape`, with the next body orbit and counter word after that many decrements. The bounds use the same number of body rounds. |

For the escape precondition, `simps!` prints the earlier-return condition as `r < p.2.2`; the source uses `r + 1 < p.2.2 + 1`. These are equivalent over naturals. The generated equations otherwise preserve the supplied arguments, including the distinct done/escape round counts and counter-word endpoints.

Adversarial boundary checks, as source-level deductions rather than claimed Lean executions:

1. A skipper that always fails still satisfies `codeSkipRepeat r 0 xs = some xs`; at one repetition the successor law gives `none`. Thus the base case does not accidentally execute the skipper.
2. `incFixed [] = none` and `incFixed [true] = none`; nevertheless `incFixed [true, false] = (incFixed [false]).map (false :: ·) = some [false, true]`. Similarly, `decFixed [false] = none` while `decFixed [false, true] = (decFixed [true]).map (true :: ·) = some [true, false]`. The length lemmas are conditional on success and make no claim that overflow/underflow produces a word.
3. A noninjective state map may identify live controls, while mapping `none` still gives `none`. All non-state fields remain unchanged. The equations therefore impose neither injectivity nor a false live-state hypothesis.
4. For a lifted write, `none` stays `none`, `some none` stays `some none`, and `some (some b)` becomes `some (some (e b))`. A blank cell stays blank. The nested option mapping is essential and is present.
5. At counter value zero the done contract requires no body rounds but retains the underflow overhead; the escape precondition would require a natural number strictly below zero and is impossible. The field equations preserve this distinction.

Verification records:

- The patch reversals check all five touched files, including both successive `CounterLoop` revisions. The review patches and committed patches have identical hunks; only the displayed blob-hash abbreviation lengths differ.
- The 21 repair/renaming names and 12 MIG-12 names have axiom prints containing only `propext`, `Classical.choice`, `Quot.sound`, or none. The supplied consumer probes report `simp=false` for all ten loop-contract and all nine renaming equations. Every new `simps` command specifies `isSimp := false`.
- Independently applying lint check 8 to the touched before/after sources drops exactly `codeSkipRepeat` and adds no name. The full-tree logs report 0 FAIL and 67 WARN over 79 files before and after; that full tree is not supplied here.
- The MIG-12 replay contains 160 distinct module entries, all with exit/error counts zero, and 80 sorry warnings in total. The round-2 replay contains 274 distinct modules with zero exit/error counts and 88 sorry warnings. Each module sequence equals its supplied order list. The static-comparison logs report zero mismatches.
- The draft probe outputs contain 52 checks for F5, 156 for C6 and 100 for U2-S, with no errors. U2-S also prints the three inherited target-sorry warnings; the pack claims zero errors for these probes, not zero warnings.
- The independently replayed CodeParser/CounterLoop screen stays at 86 declarations, 31 pairs and 9,008 reproduced characters. Its only changed row has the same 1,180-character overlap; the appended attribute changes the denominator from 1,633 to 1,750. The supplied 12-file screen similarly retains 139 pairs and 32,240 characters, with one declaration crossing the screen threshold. Some files in that wider population are not included as source, so that full screen was checked as evidence rather than independently rerun.

The supplemental independent screen on `Convention`, `CounterLoop` and `CfgRecord`, across the complete round-2 change, goes from 157 to 158 screened declarations while retaining the same 39 pairs and 16,778 reproduced characters. It finds no new pair involving the increment-width proof or another addition.

An additional MIG-12 draft record needs correction with the inventory: it describes three direct `counterLoopTM_run_escape` uses, naming `recordStep_probe_run`, `recordStep_save_run` and `recordStep_apply_run`. The supplied source has one direct invocation, at line 895 in `recordStep_save_run`; the probe lemma is a separate two-step leaf. Any intended transitive-use accounting should be stated explicitly. This is included in finding 2's inventory-accounting correction.

Lean and Lake are not installed in this audit environment. Elaboration, generated-name resolution, axiom prints and downstream compilation are therefore supplied execution evidence, not independently rerun checks. Hashes, section uniqueness, patch reversals/blob hashes, source comparisons, recorded-site pointers, inventory unions, affected-source lint, replay arithmetic and the two-file duplication screen were independently checked. No repository was accessed or modified; full commit ancestry and fresh-olean provenance cannot be independently certified from this packet.

Notation: all code identifiers and parameters retain their meanings in the bundled declarations; no additional mathematical notation is introduced.

FAIL — 0 blockers, 1 major, 2 minors, 0 notes.
