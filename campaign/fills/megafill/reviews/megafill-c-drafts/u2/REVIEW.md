# Review: megafill C's U2 brief draft (`u2s-fill-universal.DRAFT.md`), Q-U1 and Q-U2

Read-only review by the maintainer's review sub-agent, 2026-10-24. Scope: the draft at the campaign
tip `6e8db28f23386c567466dd6a7357d8ec35d1cde8` (PR #157's merge), its pre-ship
`preship-77f1eb4f/`, Q-U1 (blocking), Q-U2, and the one-brief-two-phases decision. The drafts and
the drafting report were treated as data. Every claim below cites a file under this folder
(`out/NN-*`, `probe/*`). Lean ran only through `tools/leanelab.sh` against `oleans-lslsk`, one
elaboration at a time, in the review worktree `wt/` (detached at the tip, `.lake/packages`
symlinked). The repository and `exchange/` are untouched.

**Verdict: not issuable until a prerequisite lands. Then issue after the listed edits.**
- The prerequisite is Q-U1's API PR, extended by one equation the draft missed (F1):
  `MultiTapeTM.spaceUsedByTape_eq_card`. Without it, U2-U's space clause (checkpoint 1.3) has no
  rule-10 route: the fill would hit a guaranteed escalation, and U2-U (with
  `exists_selfUniversal`, which is space-only) could not complete.
- Add `pairEncode_drop` (F2) to the same PR. It is free in replay terms.
- After the API PR lands: apply `suggested-fix.diff` (F1–F13 except F14; it applies cleanly to
  the draft at `6e8db28f`, `git apply --check` from the repository root), then re-run the
  pre-ship against the API's head as the draft's README already plans. The route probe must take `funext` at the
  tape equations (F3); `probe/QU1ApiProbe.lean`'s tail is a ready replacement.

The drafted parts hold up:
- the statements are byte-identical to the source;
- every region's line is right;
- the overlay, the order list, the roots and the base sorries reproduce exactly;
- the import probe, the route probe, the seal controls and the screen base reproduce exactly;
- Q-U1's diagnosis is right, and the proposed `simps` attribute works in place and generates the
  ten named lemmas;
- one brief in two phases is the right unit.

## Checks

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | Bases; Lean content of `77f1eb4f` = `906a9d7b` = `6e8db28f` | equal: TCSlib tree `f2c39238…`, UniversalK blob `4de5324e…`, manifest, toolchain, scripts; ancestry ok | `out/01-bases.txt` |
| 2 | Frozen statements and docstrings; regions; counts | statements byte-identical (1716–1725, 1754–1760); (a) after 11, (b) 1688, (c) 1728, (d) 1725/1760, (e) ` -/` on 1715/1753; 1,762 lines, 12 public, 39 private (all `ss_`); `uk_` unused | `out/02-frozen-regions.txt` |
| 3 | Completeness against §5 and the models | structurally complete; gaps in route citations, hazards, gate-60 carry, the input-rewind lesson | `out/03-completeness.md` |
| 4 | Import probe, re-run and extended | 77/77, 0 errors (identical output); +26 names: 20 present (route needs and named hazards), 6 expected unknowns (one is F1's missing lemma); 95 cited declarations print within the standard three, no `sorryAx` | `out/04-import-probe.txt`, `probe/U2UEImportProbeExt.*`, `probe/U2AxiomsAll.*` |
| 5 | Route probe and seal controls as drafted | 0 diagnostics; the 8 controls close unsealed and fail sealed (identical) | `out/05-route-seal-rerun.txt`, `probe/rerun-*` |
| 6 | Q-U1: no published lemma, no other route | confirmed on the tree and on both open PR heads; partial routes through `exists_forwardLoopTM` and `exists_rulerHostTM` at `t = 0` miss the state and the input position | `out/06-qu1-search.txt` |
| 7 | Q-U1's API tested in place | downstream `simps` refused (as the drafter found). In copies of the two modules it generates the ten lemmas (verbatim in 07). The drafted route and the **full seam configurations of both phases** elaborate sealed over 10 definitions; the 10 controls fail sealed only | `out/07-qu1-api-probe.txt`, `probe/QU1ApiProbe.*` |
| 8 | API PR size and replay closures | 5 modules (the two, `UniversalK`, `SelfUniversal`, the facade); with F1's equation 325 (Deterministic's closure, as #149's 324) | `out/08-api-closures.txt` |
| 9 | Route soundness, U2-U and U2-E | sound **except** the space ledger's card step (F1) and the suffix drop (F2); smaller gaps F4, F5 | `out/09-space-ledger-gap.txt`, `probe/U2SpaceGapProbe.*`, 07 |
| 10 | One brief or two | neither target follows from the other; one brief, two phases, is right; rule 4's dependency sentence needs a fix (F8) | `out/10-one-brief-or-two.txt` |
| 11 | Q-U2: the private leaf; copy hazards | within house rules; "publish at the second consumer" right; hazards unnamed (F7); the drop has no home (F2) | `out/11-qu2-leaf-and-hazards.txt` |
| 12 | Overlay and inputs | overlay = base + one import; 2 sorry warnings (1717, 1755); `fillinputs.py` and the overlay script (read first: one change) give 96 / 40 / 27 in 12, identical to the draft's files | `out/12-overlay-inputs.txt`, `out/12-fillinputs/` |
| 13 | Lint | base 0 FAIL / 68 WARN (identical); with the API and `rulerAt_iff`, check 8 clears all three names, 66 WARN | `out/13-lint-base.txt`, `out/13-lint-api-applied.txt` |
| 14 | Duplication screen (one run, under the lock) | 1,039 declarations, 785 pairs, 213,552 characters: byte-identical to `screen-base.txt` (6.3 minutes); the owned file's 14 pairs as stated (13 in-file, max 84%; one cross-file, 56%) | `out/14-screen-summary.txt`, `out/14-screen.txt` |
| 15 | Placeholders, hashes, text | both full hashes resolve and mean what the text says; `⟨its PR⟩` missing from the issue-time list; only the title over 100 columns; prescribed Lean text public-facing | `out/15-placeholders-hashes-text.txt` |

## Findings

| # | Severity | Where | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F1 | **blocker** | Route 1.3; rule 10; the API list | U2-U's space ledger needs `spaceUsedByTape = (visitedByTapeHead).card`, which has no published lemma. The route's per-tape facts are visited-set inclusions: the general seam lemma, H2-F's mirrored ledger, the frozen halt. The card corollaries of seams exist only for `Cfg.ofWords` seams, which the startup's endpoint is not. Reading `spaceUsedByTape` by its definition (unfolding, `show`, or a `card_le_card` term closing the goal definitionally) is a rule-10 violation, and a seal over the definitions the proof mentions (`spaceUsedByTape` among them) rejects it. An interval route bounds by time, not by `s`. Missed because lint check 8 counts `spaceUsedByTape_le_spaceUsed` as "a lemma beside it". | both ledger steps close unsealed, fail sealed, and close sealed with the stand-in equation (`probe/U2SpaceGapProbe.*`, `out/09`) | Add `Turing.MultiTapeTM.spaceUsedByTape_eq_card` (statement below) to the API PR, in the vendored `Deterministic.lean` beside the definition, with a header line (gate 62's pattern). Cite it in 1.3 and rule 10, and seal `spaceUsedByTape`/`visitedByTapeHead` (diff). Replay: 325 modules. |
| F2 | major | Phase 2 intro; duplication | The ruler host needs `(pairEncode α x).drop (2|α| + 2) = x`. No lemma in the closure states it. Its copies: `NDCodeSimulator`'s private `ic_input_suffix` (in the population), the local `hd` in `pairEncode_pairEncode_drop`, PathWalk's private `drop_pairEncode`, and the public `Complexity.Codec.pe_drop` (not imported). The natural `uk_` proof is a new cross-file pair, which the brief forbids ("nothing is pre-disclosed"). | `out/11`, `out/04` (unknowns) | Publish `Turing.pairEncode_drop` in `Build/InputDevice` with the API PR (no extra replay). Re-point `pairEncode_pairEncode_drop` to it, as tested in `probe/QU1ApiProbe` (0 errors). Cite it, and ledger the family for the dedup window. Or pre-disclose one `uk_` copy. |
| F3 | minor | API list; pre-ship; pitfalls | The generated tape equations take the cell (`… .workTapes i a = Fin.addCases … i a`). The draft's stand-ins take `i` only, so the route probe's proofs do not run against the landed names as written. `rulerHostCfg_inputPos` is a `Fin.mk` with a proof term. | `out/07` (verbatim `#check`s) | Diff: state "pointwise in the cell", `funext` first, `Fin.ext` for `inputPos`. Or generate `inputPos_val` for `rulerHostCfg` (tested: `↑(…).inputPos = ℓ + ↑c.inputPos`). |
| F4 | minor | Route 1.1; pitfalls | No published equation states `seamCompTM`'s (or `phaseHostTM`'s) initial state, and `U.initCfg z = (R.initCfg z).mapState Sum.inl` needs one. The startup used `{ W with q₀ := … }` with `MultiTapeTM.initCfg_with_q₀`/`runFrom_with_q₀`; the draft cites neither. | `UniversalK.lean` 1479 (`let R := { W with q₀ := Sum.inl A.q₀ }`), 1584–1595, 1661; `out/04` | Diff: route 1.1, rule 10, a pitfall. |
| F5 | minor | Phase 2 | U2-E needs one tape more than the startup has (the ruler; `K` may be `0`). That means R1 on the startup from `U`'s initial configuration, and R1 on `H` along `σ`. The draft is silent on both. | `probe/QU1ApiProbe` `r_seam_phase2` (the full phase-2 seam, sealed) | Diff: one paragraph in the phase-2 intro. |
| F6 | minor | Gate guidance | Gate 60's resolutions carry C60-1's text into "the F6 and U2-E briefs". The draft's line ("the ruler host's exits are return points") misattributes the device's property to the host and omits the host bullet (the space clause is an upper bound; `inj` is a state map, not an injection). | `campaign/gates/60-b6-f5-cont1-fill/resolutions.md` | Diff: the carry, condensed. |
| F7 | minor | Leaf; known hazards | The leaf's run lemma reads the header cells that `UniversalStartup`'s private `universal_pair_get`, `universal_pair_separator` and `universalPrefix_bits` read; these are unnamed hazards. The leaf is specified only from input position 1 on a blank ruler, which does not serve its named second consumer (a two-pairing header). | `out/11`; `Hierarchy.lean` 115–122 | Diff: the generic run-lemma form, reading by the suffix (`inputSymbolInner`, `List.getElem_drop`, `pairEncode_eq`), and the hazards named. |
| F8 | minor | Rule 4; 1.4 | "Phase 2 depends … only on its seam (1.1)" contradicts 2.3 ("phase 1, step 2") and 2.4 ("phase 1's converse argument for `L`"). | draft lines 289–295, 326 | Diff: the `L`-level lemmas are input-generic `uk_` lemmas of 1.2/1.4; rule 4 says so. |
| F9 | minor | Rule 10, seal list | "`Lockstep`'s consumers' definitions you reach" is vague. The list omits definitions the route reaches (`embedEmitCfg`, `Cfg.mapState`, `spaceUsedByTape`, `visitedByTapeHead`, `FinTM.ComputesInTime`, `pairEncode`, `Cfg.inputSymbol`). | 07's 10-definition seal | Diff: a concrete list. |
| F10 | note | Hosts; checklist | Megafill A's input-rewind lesson is only implicit. | backlog 1479–1481 | Diff: say that none is needed and that, if one is, the fill cites `Turing.inputRewindTM` (in the closure, `out/12`). |
| F11 | note | ⟨IN-FLIGHT⟩; comment | #156's head moved during this review to `0e5f210b`. It now touches `Build/Seam`, `Build/StepBlock` (both upstream of the owned file), `Build/WindowRun`, `Build/OracleSim`, `CodeSimulator` and `SpaceComplexity/Inclusions`, with no statement change beyond its two new lemmas. "`Build/Seam` only" is stale. The issue-time list omits `⟨its PR⟩`. | `out/01`, `out/08` | Diff (comment): if #156 is in the issue base, its two lemmas become citable and go into the probe. Re-run the pre-ship anyway. Whichever of #156 and the API PR merges second replays on the merged tree. |
| F12 | note | Cited infrastructure | The probe lacks about 20 names the route needs (`initCfg_with_q₀`, `embedEmitTM_frame`, `embedEmitCfg_mapState_eq`, `inputSymbolInner`, `List.drop_left`, …), all present. Notably the leaf writes, but the probe's "leaf one-step lemmas" are the non-writing ones; the writing step is `step_of_tapeAction_write` (present, with `moveInputPos_pos_of_ne_right`). | `out/04`, `probe/U2UEImportProbeExt.lean`, `probe/U2LeafNames.*` | Stage the extended probe at issue (both files' lists, plus the API's names). The diff names the writing step in 2.1. |
| F13 | note | Checklist | U2-E's construction runs the startup first, then the scan; the frozen sketch (i) lists them the other way round. As for the startup (gate 63 m1), an `**Implementation.**` paragraph will be wanted at integration. Gate 26's recorded sanity lemmas (halt equivalence, the startup-to-forwarding equality) come out of the route anyway. | `UniversalK.lean` 1743–1747; gate 26 resolutions | Diff: REPORT.md proposes the paragraph. |
| F14 | note | Population | The public `Complexity.pairEncode_getD` (`SpaceComplexity/Logspace/InputAccess`, outside the closure and the population) states the header's cells. | `out/11` | Optional: add that file to the population at issue (re-measure the base). Not in the diff. |

## Q-U1: recommendation (verified in `probe/QU1ApiProbe.lean`)

**Do the API PR before issue, extended by F1 and F2.** Its exact text and what it generates:

1. `Build/StepBlockForward.lean`, right after `forwardLoopCfg` (line 78). The definition is a
   `where` structure instance, so `simps` applies. The file's "Main definitions" list can name the
   lemmas.
   ```lean
   /-! The encoding's fields as equations, without the `simp` attribute. -/
   attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
     forwardLoopCfg
   ```
   It generates, verbatim from `#check`:
   - `forwardLoopCfg_state : (forwardLoopCfg entry M c).state = Option.map (fun x => entry) c.state`;
   - `_inputPos : … = c.inputPos`;
   - `_workTapes (i : Fin (k + 2)) (a : ℤ) : (…).workTapes i a = Fin.addCases (motive := fun x => ℤ → Option Bool) c.workTapes (fun j => if j = 0 then FinTM.bufferTape (tableBitsK M.tr) else StepBlock.summaryCells none ((Option.map unaryFin c.state).getD [])) i a`;
   - `_workTapePos (i) : … = Fin.addCases c.workTapePos (fun x => 0) i`;
   - `_output : … = c.output`.

   All are in `Turing.StepBlock`.
2. `Build/InputDevice.lean`, right after `rulerHostCfg` (line 741). The definition is an anonymous
   constructor, so `simps` applies.
   ```lean
   /-! The layout's fields as equations, without the `simp` attribute. -/
   attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
     rulerHostCfg
   ```
   It generates:
   - `rulerHostCfg_state : … = q`;
   - `_inputPos : … = ⟨ℓ + ↑c.inputPos, ⋯⟩`;
   - `_workTapes (i) (a) : … i a = Fin.lastCases (motive := fun x => ℤ → Option Bool) rt c.workTapes i a`;
   - `_workTapePos (i) : … = Fin.lastCases rp c.workTapePos i`;
   - `_output : … = c.output`.

   **Option:** `inputPos_val` in place of `inputPos` gives
   `rulerHostCfg_inputPos_val : ↑(…).inputPos = ℓ + ↑c.inputPos` (tested on a copy), the form the
   route reads.
3. **F2, same file, before `pairEncode_pairEncode_drop`** (whose proof then drops its local `hd`
   and ends `← List.drop_drop, pairEncode_drop, pairEncode_drop`; tested):
   ```lean
   /-- **The payload after the header.** Dropping the header of length `2|u| + 2` from
   `pairEncode u x` leaves `x`: the ruler device's `z.drop ℓ = y` for the code-first input.

   **Proof sketch.** The pairing is the header `pairEncode u []` followed by `x`, and that header
   has length `2|u| + 2` (`Turing.length_pairEncode`). -/
   theorem pairEncode_drop (u x : List Bool) : (pairEncode u x).drop (2 * u.length + 2) = x := by
     have split : pairEncode u x = pairEncode u [] ++ x := by
       rw [pairEncode_eq, pairEncode_eq, List.append_nil]
     have width : (pairEncode u []).length = 2 * u.length + 2 := by
       rw [length_pairEncode, List.length_nil, Nat.add_zero]
     rw [split, ← width, List.drop_left]
   ```
   Its text equals `ic_input_suffix`'s, so the screen will pair them. Ledger the pair, with
   `drop_pairEncode` and `pe_drop`, for the dedup window (re-point `ic_input_suffix` after C1's
   landing).
4. **Optional, same file, after `RulerAt`** (it clears check 8 for the file; U2 does not read it):
   `theorem rulerAt_iff … : RulerAt ℓ r d i ↔ 0 < ℓ ∧ ℓ ≤ z.length ∧ z.drop ℓ = y ∧ d.inputPos.val = ℓ + i.val ∧ ∀ p : ℤ, -1 ≤ p → p ≤ (ℓ : ℤ) → d.workTapes r (d.workTapePos r + p) = FinTM.bufferTape (List.replicate ℓ true) p := Iff.rfl`
   (tested).
5. **F1, `Deterministic.lean` (vendored), beside `spaceUsedByTape`**, with a line in the header's
   list of local modifications:
   ```lean
   /-- The space on one tape is the number of distinct cells its head visited. -/
   theorem spaceUsedByTape_eq_card (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
       tm.spaceUsedByTape cfg t i = (tm.visitedByTapeHead cfg t i).card :=
     rfl
   ```
   Tested as a stand-in: with it, both ledger steps close under the seal (`probe/U2SpaceGapProbe`).

**Size:** items 1–2 are 8 lines, items 3–5 about 25 more, across two or three files. No statement
changes. **Replay:** items 1–4 replay 5 modules (`out/08`); item 5 replays Deterministic's
downstream closure, 325 modules. No other megafill C item needs these equations: neither name,
nor `RulerAt`, nor `spaceUsedByTape`, occurs in the C1, B5a or G4 drafts or owned files
(`out/06`, last section).

## Q-U2: recommendation

**Agree.**
- One private leaf, with a docstring naming the missing row, is within the house rules: the
  policy's hand-built-machine sentence, startup-cont1's leaves, configclock-cont2's list, H5's own
  `rd_test`.
- No public row writes a header-length ruler. That covers the tree and both PR heads; `rd_test`'s
  docstring already records that no catalog row moves the input head together with a work head.
- Keeping it private until `space_universal` is briefed matches the "harvest before a second
  consumer is briefed" rule.

Refinement (F7, in the diff): state the run lemma for one header from any input position with a
ruler offset. Then `space_universal`'s two-pairing header is two runs, and the promotion is a
visibility change. Also read the cells by the suffix, not by `UniversalStartup`'s index lemmas.

## Decisions for the user
1. **F1, the space equation.** Choose one:
   - (a) in the Q-U1 API PR: one PR, one 325-module replay;
   - (b) a separate API PR: Q-U1 replays 5 now, and this one replays 325;
   - (c) issue without it: U2-U's checkpoint 1.3 escalates, U2-U and `exists_selfUniversal` stay
     open, and U2-E is unaffected. The cover's "a partial (U2-U alone) is useful" then needs
     rewording.

   Recommendation: (a), or (b) if the 5-module PR should go first.
2. **F2, the suffix drop.** Publish `pairEncode_drop` in `Build/InputDevice` with the API PR and
   ledger the drop family (recommended), or pre-disclose one `uk_` copy in the brief.
3. **API details.** `inputPos` or `inputPos_val` for `rulerHostCfg`; whether to include
   `rulerAt_iff`.
4. **At issue:** apply `suggested-fix.diff`, fill the placeholders (`out/15`), stage the extended
   probes, and re-run the pre-ship against the API's head (and #156's, if merged).
