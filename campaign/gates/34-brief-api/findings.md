External audit of PR #118 — the brief-inventory API

Audited the supplied `brief-api-bundle.md` as a self-contained packet, with one agent and no sub-agents. Its SHA-256 is `ea12197afca2ee4fd21d1187a279629622f58a8218f9b362650b02f36e7ad6bf`, exactly the commissioned value. All 100 section paths are unique.

The added equations are faithful. The gate fails because the inventory does not yet establish the promised no-unfolding route for the canonizer's continuation 6. These are API-completeness findings, not counterexamples to the new Lean statements.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `CodeParser.lean` · `codeSkipRepeat`; `DefInventory.lean.txt`; C6 draft, route item 3 | The generic repetition proof needs a documented case API that the inventory misses. | C6 explicitly requires proving that the counter loop decides `codeSkipRepeat r (counterValue c)`. Its zero-round and successor-round cases need the repetition's zero and successor laws. `C6-inventory.out` checks `codeSkipRepeat` itself but omits it from its definition inventory; `DefInventory` traverses each seed's **type**, without including the seed itself. `lint-tip.txt` explicitly lists `codeSkipRepeat` as lacking a published named lemma. The judgment table never disposes of this name. The inherited private `canonSkipRepeat_add` and `_mul` are composition laws, not the missing zero/one-step semantics. | Publish and probe documented `codeSkipRepeat_zero` and `codeSkipRepeat_succ` equations beside the definition. Include explicitly named route definitions themselves in the inventory, not just definitions appearing in the types of cited constants. If compiler-generated equation names are intended as the API, identify and validate their exact statements and document that exception to the stated publication rule. |
| 2 | major | `Build/CounterLoop.lean` · `RoundContract.counterLoopDone`, `RoundContract.counterLoopEscape` | The recorded C6 round-contract route still lacks the contracts' field equations. | Both constructors occur in `C6-inventory.out` and in the per-lemma dependencies of `counterLoopDone_traj` / `counterLoopEscape_traj`. `NOTES.md` expressly cites those trajectories as C6's use of `counterLoopBody`. The source publishes the two constructors and their `_traj` theorems, but no `pre`, `time`, `post`, `lo`, or `hi` equations. Applying `Contract.traj_iff` still leaves the opaque constructor's precondition and time. `Contract.ofSegment_*` cannot expose the wrapper without first reading that wrapper's definition. Check 8 misses this because the `_traj` names satisfy its prefix heuristic. | Publish the five field equations for each constructor, without the simp attribute, and probe their use from C6. Alternatively, explicitly narrow the recorded route to the raw run/segment theorems and demonstrate the complete replacement route without using the unexposed wrappers. Adding `counterLoopBody`'s fields alone does not establish the claimed coverage. |
| 3 | minor | `audits/evidence/brief-api/NOTES.md` · first-commit generated-name/axiom count | The handwritten-theorem count is incorrect. | `brief-api.patch`, `freeze.log`, the probes, and `screen-bodylen.txt` contain **11**, not 15, handwritten theorems. With 9 generated equations, the first commit adds 20 declarations. The second adds 8 handwritten plus 5 generated, giving 33 altogether. | Change 15 to 11; retain the correct generated count of 9. |

The concrete equations required by finding 1 are:

```lean
codeSkipRepeat r 0 xs = some xs
codeSkipRepeat r (n + 1) xs = (r xs).bind (codeSkipRepeat r n)
```

Here `r` is a skipper, `xs` an input word, and `n` a repetition count. These are proposed API statements, not newly compiled declarations. Finding 2 concerns, for example, proving the concrete precondition of `(R.counterLoopDone e)` and evaluating its time before applying its trajectory theorem. A theorem about that contract's trajectory does not itself expose those fields.

Answers to the pack's six questions:

| Question | Result | Basis |
|---|---|---|
| 1. Faithfulness | Satisfied | All 19 handwritten statements restate their definitions; the 14 generated field equations agree with the source projections and the printed statements. The three `decFixed` cases exhaust its inputs. No missing hypotheses or false new statement found. |
| 2. Inventory completeness | Not satisfied | Findings 1–2 identify the C6 omissions. No additional missing equation was identified for the described U2-S, F3, F5, or G4 routes. The detailed judgment review follows below. |
| 3. No behavior change | Satisfied for the supplied patches | Reversed both patches against the bundled sources. Every reconstructed old and supplied new file matches its patch's Git blob-hash prefix, for all eight files. The actual hunks contain 77 and 72 insertions, respectively, with zero deletions. They add theorem declarations, documentation, and four `simps` commands with `isSimp := false`; they change no existing statement or definition and introduce no admission. |
| 4. Publication rule and lint | Satisfied for the additions; incomplete for the routes | New handwritten equations sit beside their definitions, with formula-bearing docstrings; generated equations are attached there by `simps`. Independently running check 8's implementation on the affected sources reproduces drops of 10 and 6 names, with no additions. A clean heuristic result does not establish field coverage: finding 2 is a concrete false negative. The remaining `roundStop` warning has the route-appropriate `not_mem_roundStop` characterization. |
| 5. Duplication | Satisfied | Independently reran the supplied v3 screen sequentially on both populations, before and after. All four complete outputs match the supplied logs. The first population stays at 404 declarations / 167 pairs / 64,426 characters. The second changes from 68 / 21 / 5,700 to 71 / 28 / 6,213, with nine new and two removed pairs. The new pairs are segmentation artifacts, not newly copied proof bodies. |
| 6. Records | Satisfied subject to finding 3 and the execution limit below | Replay logs contain 311 and 86 distinct module entries, respectively, all with exit 0 and errors 0. Their summed sorry counts are 94 and 56. The second replay list is a subset of the first; the static-comparison logs report zero mismatches. The source/patch and screen attestations were independently reproduced. |

Lean and Lake are not installed in this audit environment. Elaboration, generated-name resolution, axiom prints, and the full downstream replays were therefore reviewed as supplied evidence, not independently rerun. The attachment hash, section inventory, patch reversal and blob hashes, affected-file lint comparison, replay-log arithmetic, and duplication screens were independently checked. No repository was accessed or modified. The full merged-tree ancestry claim is not independently certified by a self-contained source packet.

Review of every substantive judgment in `NOTES.md`:

| Judgment group | Audit disposition |
|---|---|
| U2-S: `bufferedCompTM`, `universalPrefixTM`, `prefixCanonTM` | The added tape-count/state equations and composite equation supply the missing placement data. Existing `prefixCanon_run` and buffered-configuration fields expose the endpoint. |
| `VirtualTag`; F5's `vhostBuffer` and `vhostBank` | The added characterization and index equations are exact. F5's actual ruler encoding and local input predicates are in its owned file; the virtual-input host supplies a model, not a requirement to unfold its implementation. `Lockstep` is a structure with public fields. |
| F3: `RecSym.digitEmb`, `posWidth`, `binDigits` | The digit equation connects the lifted clock cells. `record_pos_lt`, `recordLength_eq`, `joinFields_cfgRecord_length`, `cfgRecord_length`, `cfgRecord_field_ne_nil`, and `joinFields_length` supply the width, nonempty-field, and length arithmetic without expanding `cfgRecord`. The new width/digit equations are faithful additional coverage. |
| C6: `counterLoopBody`, `stateWord` | These additions are useful and correct, but do not finish C6's inventory: findings 1–2 remain. The Bool layout of `counterLoopCfg` is already exposed by `counter_cfg_eq`; this audit does not claim that layout is missing. |
| `decFixed` for #117 / MIG-12 | All constructors are covered by the three new equations, including underflow on an all-false word. |
| `tapeAction`, `inputMoveAction`, `catalogTrace` | Accepted for the routes through `step_of_tapeAction_move`, `_write`, `step_of_inputMoveAction`, and `catalog_trace_run`. These are semantic interfaces to the local leaves or row traces; the routes need not inspect the action constructors. |
| Hydroxyi's `simCfg`, `stg`, `wr`, `PB`, `markI` | Accepted for the specified primary route through `cleanTM_run`. Its conclusion already supplies the halt, output, cleared tapes, and returned heads. The restart lemmas remove the need to read `cleanTM`'s initial state. This acceptance does not certify an additional route through the internal stage lemmas if such a fallback is later activated. |
| `tableBitsK`, `actionBitsK`, Encoding's bit words | Accepted as opaque data on these routes. U2-S redistributes the word exposed by `serializeK_eq`; it does not interpret table entries. C6 can consume its already-proved local record validator. |
| `StepBlock.Rep`, `SkipPh`, `exit`, `workReadsK`; `codeSkipActionK`, `codeSkipFin`, `codeSkipState`, `codeSkipTable2` | The broader cont4 probe contains material outside cont6's remaining task. The existing local `exists_canonUnaryTM`, `exists_canonRecordTM`, `canonSkipFin_iff`, `canonSkipAction_eq`, and `canonSkipTable_eq` support treating these as already handled. **This exclusion does not extend to generic `codeSkipRepeat`**, which C6 explicitly needs. |
| G4: `Round`, `Segment`, `HeadBox`, `Cfg.SameOutside`, `Contract.Traj` | The new iff lemmas expose exactly the required anchor, cut, head, frame, and trajectory obligations. They allow two escapes and a nontrivial head relation; `Round.of_cut` alone does not. |
| G4: `roundOrbit`, hulls, `Cfg.bindState` | Zero plus the existing successor law covers the orbit; the hull equations expose the finite min/max including the final orbit point. The five redirect fields expose `Contract.inPhase`'s endpoint. |
| G4: `Contract.Positive`, `roundStop`, `Contract.Frames` | Accepted for this route through the positivity constructors, the time-zero characterization, the exact nonmembership characterization, and `frames_iff`. This is route-specific acceptance, not a claim that `positive_of_not_mem` and `not_mem_of_positive` constitute an unconditional iff when there are no admissible starts. |
| G4: `scanMap`, `scanShift`, `mealyRun` | Accepted. `scanTM_contract_post` uses `scanResult`; `scanResult_map`, `_shiftRight`, and `_shiftLeft` expose the required map/repacking behavior without reading the Mealy implementation. |
| G4: zone layer, row contracts, `framedContract`, `seekPost`, `sweepPost`, combinators | The bundled source and enumerations cover the route's contract fields, layout boundaries, zone cases, and compositions. The partial's old direct uses of `zonedTape`, `zoneSlotOf`, and `zoneCapacity` can be repointed to the cited equations. No additional required foreign definition lacking a route-appropriate interface was found here. |

Restatements of the definitions whose API this PR extends, checked against their bodies and the new statements:

| Definition | Mathematical content exposed by the new API |
|---|---|
| `bufferedCompTM` | Its tape count is `M₁.k + (1 + M₂.k)`; its state type is `Option M₁.State ⊕ (Unit ⊕ (M₂.State × Bool))`. |
| `universalPrefixTM` | Zero work tapes and state type `Option Bool`. |
| `prefixCanonTM` | The buffered composite of `universalPrefixTM` and the supplied canonizer. |
| `VirtualTag` | The tag is false at position zero and true at position `n + 1`; neither condition restricts an interior position. |
| `vhostBuffer` | The first tape, `Fin.castAdd m (0 : Fin 1)`. |
| `vhostBank` | Source tape `i` is placed at `Fin.natAdd 1 i`. |
| `RecSym.digitEmb` | A Boolean maps to its `RecSym.digit` constructor. |
| `binDigits` | The first `w` test bits of `v`, in increasing bit-index order. |
| `posWidth` | The length of `Nat.bits (n + 1)`. |
| `counterLoopBody` | Replace the control by the live anchor; retain the input position and output; select the first `k` host tapes and heads through `Fin.castSucc`. |
| `decFixed` | Empty input underflows; a leading true becomes false with the tail unchanged; a leading false becomes true if recursive borrowing from the tail succeeds. |
| `stateWord` | Tape index zero carries the supplied word; every other tape carries the empty word. |
| `Cfg.SameOutside` | Every cell outside the designated footprint has the same content in the final and initial configurations. No head, state, input-position, or output equality is asserted. |
| `HeadBox` | Every work-head coordinate lies in its specified closed integer interval. |
| `Segment` | Exact endpoint after the given time, forbidden-state avoidance strictly before that time, and the head relation at every time including both ends. |
| `Round` | A live anchor start, strictly positive duration, exact endpoint at the anchor or an escape, avoidance of halt/anchor/escapes strictly inside, and the head relation through the endpoint. |
| `roundOrbit` | Repeated execution of the configuration-dependent round time; its zeroth point is the initial configuration. |
| `RoundContract.hullLo` | The least of the first `n` round lower bounds and the final orbit point's head, separately on each tape. |
| `RoundContract.hullHi` | The greatest of the first `n` round upper bounds and the final orbit point's head, separately on each tape. |
| `Contract.Traj` | For every admissible start at the entry, the whole head vector satisfies the given relation at every time through the contract's time. |
| `Cfg.bindState` | Bind the optional control through the supplied partial state map; keep all four other configuration fields. |

Adversarial boundary checks (source-level deductions, not claimed Lean test executions):

1. Empty and borrowing counters: `decFixed [] = none`; hence `decFixed [false] = (decFixed []).map (true :: ·) = none`. Also `decFixed [false, true] = (decFixed [true]).map (true :: ·) = (some [false]).map (true :: ·) = some [true, false]`. Thus the false-leading equation handles both successful borrowing and underflow.
2. Zero duration: `round_iff` requires `0 < 0`, so a zero-time round is impossible. In contrast, `segment_iff` at zero requires the two configurations to coincide and the initial head vector to satisfy the relation; its strict cut is vacuous. The new lemmas preserve that intended distinction.
3. Zero rounds in the hull: the range contains only zero; the strict comparison with zero is false; `roundOrbit_zero` identifies the orbit point with the start. Both hull ends are therefore exactly the initial head coordinate, not an empty-set extremum.
4. Empty tape bank and empty virtual input: `stateWord 0` has no tape index to evaluate, and `HeadBox` on zero tapes is vacuous. For input length zero, the two virtual boundary positions remain distinct (zero and one), so `VirtualTag` consistently requires opposite tags.
5. Halted redirect: binding `none` gives `none` and preserves tapes, heads, input position, and output. A partial redirect is not incorrectly asserted to be injective or total.

Useful permanent sanity statements would record the zero-round hull formulas and the borrowing/underflow examples above, using only the published API. More importantly, the repair should include consumer probes that prove the generic repetition base/step obligations and expose every field of both counter-loop contracts without unfolding their definitions.

The second commit's screen explanation is substantively correct. The parser reads a declaration up to the next declaration, so the new `Iff.rfl` lemmas inherit following namespace/section openings and variable binders. Replaying `pairtext.py` reproduces all nine supplied explanations exactly. The phrase 'exactly such a binder line' is slightly loose: one shared fragment includes the suffix of `namespace Segment`, and others contain binder fragments. None contains a copied nontrivial proof body. The two removed pairs likewise lose the following binder text from `Traj`; their small remaining shared expression does not meet the screen threshold. This is not a new duplication-debt finding.

Notation: code identifiers and parameters have the meanings in the bundled declarations; no additional mathematical notation is introduced.

FAIL — 0 blockers, 2 majors, 1 minor, 0 notes.

