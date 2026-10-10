# §12.6 framed catalog contracts — fill-gate findings

**Verdict: PASS — 0 blockers, 0 majors, 2 minors, 5 notes. The fill gate closes under the stated rule.** The generalized traces, five canonical specializations, four space rows, and authorized freeze/reordering pass. The minors concern duplication accounting inside the already acknowledged sibling family; they require documentary corrections, not another proof fill.

Audit date: 2026-10-10. Requested branch/pin: `complexity/arora-barak-ch3-4`, `9a492650`. Evidence is the supplied `s12-framed-fill-bundle.md`, SHA-256 `ea9b8b7d9446e921645a601d809b34eecbc697ba1af615595a9435e7f88f835d`. Line references below are to the extracted final `Build/Catalog.lean`, not the bundle. This is a surface audit; the supplied kernel replay is treated as maintainer evidence.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F1 | minor | `audits/s12-framed-agent-reports/fill-REPORT.md` · private-declaration summary; pack question 6 | “Zero new copied declarations or proof bodies” overstates the result. New repeated proof text exists, but it stays within the acknowledged §12 sibling family. | Independently reconstructed all copy-text comparisons involving a changed declaration. The logs' 16 new directed pairs and 5,520 matched characters are correct, including transfer-framed → copy-framed `403/415`, success-framed → overflow-framed `617/686`, two space-row pairs, and the increment configuration pair. No parallel canonical trace survives; no new file or routine family is implicated. The existing common-scanner resolution remains applicable. | Qualify the report: no additional canonical trace or new copy family; the binding census is unchanged, while the disclosed sibling repetition remains debt under 12.2c item 5. Include the generalized traces, framed consequence proofs, canonical specializations, and space wrappers in that factoring work. No renewed acknowledgment or major is required under amended failure mode 5. |
| F2 | minor | `audits/evidence/s12-framed-fill/copytext-diff.txt` · “CHANGED shares”; pack text-screen attestation | There are **23**, not 21, changed persistent pairs. Two denominator-only changes were omitted. | `compareTM_spaceUsedByTape` → `copyTM_spaceUsedByTape`: `315/473 = 67%` → `315/581 = 54%`; `incrementTM_spaceUsedByTape` → `clearTM_spaceUsedByTape`: `244/318 = 77%` → `244/434 = 56%`. Both occur in the before/after logs. Their numerators are unchanged, so the headline matched-character totals remain correct. | Add both rows and replace “21” with “23” in the diff and pack. Compare both numerator and denominator when generating the changed-pair list. This is accounting within the acknowledged family, hence minor. |
| F3 | note | `Build/Catalog.lean:356–932` · 14 generalized privates and `catalogTape` | The single generalized trace per routine requirement and binding transition route are satisfied. | All 15 blind restatements are recorded below. Copy/transfer share the same `catalogCopyF` and the same `catalog_copy_forward` application. Both increment verdicts invoke `catalog_increment_trace`. The generic trace induction is unchanged. Successful increment turns at the first false cell and never visits the following cell. | None. Retain the shared traces during the planned refactor. |
| F4 | note | `Build/Catalog.lean:1212–1620` · five run rows and four space rows | All nine adaptations are genuine specializations; their statements are unchanged. | The run rows directly cite their framed counterparts at `Cfg.ofWords`. Transfer/copy use `hdst`; successful increment proves equal width. The space rows use the generalized all-time traces and the unchanged interval/singleton arguments, including the stationary tail. | None. |
| F5 | note | `audits/evidence/s12-framed-fill.patch` · freeze and reordering | The attached patch has precisely the authorized surface delta. | Exact reverse/forward patch replay reproduces both Git blob IDs. All 44 public signatures and docstrings are byte-identical; exactly 14 public bodies change and the other 30 declarations are unchanged in full. Private count is `384 → 384`, with the advertised removal, addition, and 14 changes. Imports, generic trace declarations, and all compare declarations are unchanged. | None. |
| F6 | note | `Build/Catalog.lean` · docstrings and module status | The disclosed status-label staleness is the only substantive documentation staleness found in the audited Catalog surface. | All 37 “fill pending” tags remain from the baseline, together with its skeleton-status header. The generalized private descriptions match their phase invariants under the trace hypotheses. Each framed “specializes to” sentence is now realized by the corresponding canonical proof. | Complete the already queued doc-only status refresh. No theorem or proof repair. |
| F7 | note | Audit packet · provenance and replay attestations | Independent byte/source checks and maintainer execution claims must remain distinguished. | The source matches the delivery SHA-256 and patch blobs. The 44-name axiom log is complete and standard-only. Kernel execution, the six-file census generator, original ZIP checksums, and the relationship to requested commit `9a492650` were not independently replayed: the bundle lacks the full repository, original ZIP, and screening scripts; its pack names tip `e44b5656`. | Preserve the existing replay evidence. When recording this audit at the requested tip, identify its Catalog blob as `8d8cb704798f02af6014f8f27fa05075930c5521`. Do not describe this report as a fresh Lean run or full repository-history verification. |

**Blind restatements.** These were recorded from a comment-stripped source before reading the changed private docstrings or the statement-gate findings. Fields not explicitly updated retain their values from `d`. All intervals in tape updates are half-open; head-containment intervals are inclusive. Phase interpretations use the corresponding trace hypotheses; the auxiliary definitions are total even at indices outside the phase range.

| Declaration · final line | Literal restatement from the body/type |
|---|---|
| `catalogTape` · 356 | At integer coordinate `q`, return the word buffer at `q-a` when `a ≤ q < a+w.length`; otherwise return the arbitrary background `f q`. No assumption on the sign of `a`, support of `f`, or exterior blanks. |
| `catalog_write_take` · 363 | If `r < w.length`, updating the next cell `a+r` to `some w[r]` extends the prefix overlay from `[a,a+r)` to `[a,a+r+1)`, preserving its arbitrary background elsewhere. |
| `catalogClearF` · 379 | Set control to `sweep` and move only head `i` from its original position by `r`; preserve all tapes, input position, and output. |
| `catalogClearR` · 386 | Set control to `rewind`, blank tape `i` from its original head plus `r` up to its original head plus `n`, and put that head at original head plus `r-1`. Other tapes and heads are unchanged. |
| `catalog_clear_trace` · 398 | For arbitrary `d` in `sweep`, with tape `i` equal to the buffer of `w` at relative offsets `-1` through `w.length`, the run at every time is the generic trace of these configurations. Its final configuration has control `done`, the word interval erased, original heads, and the remaining fields of `d`. |
| `catalogCopyF` · 462 | Set control to `sweep`, overwrite the destination prefix of length `r` with the relative buffer of `w`, and move the source and destination heads by `r` from their respective original positions. Other cells and fields are preserved. |
| `catalogCopyR` · 472 | Keep the tape contents of `catalogCopyF` at `w.length`, set control to `rewind`, and place each active head at its original position plus `r-1`. |
| `catalogTransferR` · 481 | Use `catalogCopyR`, additionally blanking the source suffix from relative `r` through `w.length` exclusive. With distinct indices, the copied destination is preserved. |
| `catalog_copy_forward` · 489 | With distinct source/destination, the delimited source word in arbitrary `d`, and `r < w.length`, one copy-machine step sends the forward configuration at `r` to that at `r+1`. No premise on `d.state` is needed because `catalogCopyF` supplies the state. |
| `catalog_copy_trace` · 514 | Under the same source/distinctness premises and `d.state = some sweep`, every run time follows the generic copy trace. It ends at original heads with only the destination word interval overwritten; the source and arbitrary destination exterior are preserved. |
| `catalog_transfer_trace` · 563 | Under the same premises, transfer uses exactly the copy forward configurations and the transfer return configurations. It ends at original heads with the source word interval blanked and destination word interval overwritten, preserving the exterior frame. |
| `catalog_write_middle` · 789 | Updating the cell `z+pre.length` of the overlay of `pre ++ a :: rest` to `some b` gives the overlay of `pre ++ b :: rest`, with the same background. |
| `catalogIncF` · 814 | Set control to `run`; overlay the selected tape with `replicate r false ++ replicate (p-r) true ++ tail.elim [] (false :: ·)` at its original head, and move that head by `r`. The trace uses `r ≤ p`. |
| `catalogIncR` · 825 | Overlay the selected tape with `replicate p false ++ tail.elim [] (true :: ·)`, set control to `rewind tail.isSome`, and put its head at original head plus `r-1`. |
| `catalog_increment_trace` · 839 | If arbitrary `d` is in `run`, carries delimited `w`, and `w = replicate p true ++ tail.elim [] (false :: ·)`, every run time is the generic increment trace with length parameter `p`. Its final tapes are the return overlay, all heads are restored, and control is `done tail.isSome`. `none` covers all-true and empty overflow; `some rest` covers success at the first false bit. |

These match the private docstrings. In particular, “arbitrary configuration” is real: there is no canonical-origin, reachability, finite-support, empty-output, initial-input-position, or blank-destination requirement. The only canonical trace left in this region is compare's unchanged trace, explicitly outside the framed scope. `catalog_erase_take` is removed; no affected routine retains a canonical predecessor under another name.

**Route fidelity and boundary behavior.** The unchanged `catalog_trace_run` consumes exactly five transition obligations: forward step, turn, return step, entry, and stationary final step. Each affected routine discharges those obligations using its framed configurations. Transfer uses the copy forward lemma directly because the two sweep actions are definitionally identical.

Put `n = w.length`; on successful increment put `p = (w.takeWhile id).length`. The existing split/value lemmas give

\[
\begin{aligned}
\texttt{incFixed w = some v}
&\Longrightarrow w=\texttt{replicate }p\ \texttt{true}++(\texttt{false}::\texttt{rest}),\\
&\hspace{18mm}v=\texttt{replicate }p\ \texttt{false}++(\texttt{true}::\texttt{rest}),
\quad |v|=n,\quad p<n;\\
\texttt{incFixed w = none}
&\Longrightarrow w=\texttt{replicate }n\ \texttt{true}.
\end{aligned}
\]

The success proof explicitly identifies the split length with `takeWhile`; the overflow proof identifies it with `w.length`. Let `m=n` for transfer/copy/clear/overflow and `m=p` for success. Reading the actual trace definition gives

\[
\text{relative head offset at time }t=
\begin{cases}
t,&0\le t\le m,\\
2m-t,&m+1\le t\le2m+1,\\
0,&t\ge2m+2.
\end{cases}
\]

Indeed, the return index is `r = 2*m+1-t`, and its integer head offset is `r-1 = 2*m-t`. Thus at time `m` the head is at `m`, at `m+1` it is at `m-1`, at `2*m+1` it is at `-1`, and the next step restores offset zero. The state is a forward state, then a rewind state, then the live `done` anchor; neither increment exit appears in either earlier phase.

At return index `r`, transfer/clear have erased exactly `[r,n)`. On success, the turn **writes at offset `p` and then moves left**; it does not move to `p+1`. These facts agree with `Action.apply` at `Configuration.lean:197–205`, which updates the old head coordinate before adding the movement. Inactive tapes receive `(none,0)`; every relevant action has input movement zero and emits nothing. The complete record equalities therefore preserve input position, output prefix, inactive tapes/heads, and all exterior cells, including at negative absolute coordinates. All final actions stutter; these are live returns, not genuine halts.

Independent finite semantic checks compared the transition tables against the generalized phase formulas for every Boolean word of lengths 0–4 in three arbitrary frames: **372 configurations and 4,896 time points**, including five steps after exit. Counts were 93 transfer, 93 copy, 93 clear, 78 successful increment, and 15 overflow. Frames used negative/displaced/equal coordinates on distinct tapes, reversed source/destination indices, nonblank periodic backgrounds, occupied destination delimiters, varying input positions, and a nonempty output. Tape equality compared all finite deviations over the common infinite backgrounds. All checks passed. Another **882 checks** exercised the two tape-update identities, including empty prefixes, negative origins, and writes that preserve or flip the bit. These checks are not Lean executions or universal proofs.

Concrete boundary instances also agree with the statement gate's route:

| Routine/helper | Adversarial instances checked | Consequence |
|---|---|---|
| Transfer and copy | `[]`; `[false]`; `[true,false,true]`, with hostile destination contents | Exact times 2, 4, 8; destination delimiters survive; a stored false is copied as a nonblank bit. Transfer erases only its source interval; copy preserves it. |
| Clear | `[]`; `[false]`; `[true,false,true]`, including a negative start | Exact times 2, 4, 8; only the word interval is erased. The empty path is `0,-1,0`. |
| Successful increment | `[false,true,true]`; `[true,true,false]`; `[true,false,true]` | Carry lengths 0, 2, 1 and times 2, 6, 4. The respective maximum relative positions are 0, 2, 1; the unvisited suffix remains intact. |
| Overflow | `[]`; `[true]`; `[true,true,true]` | Times 2, 4, 8; result contains zero, one, or three stored false bits, not erased cells. |
| Overlay/update helpers | Empty word; negative origin with occupied exterior; first/last-cell update with `a=b` or `a≠b` | Empty overlay is identity; exterior values survive; prefix extension and middle replacement agree extensionally. |

**The five canonical specializations.** Each proof sets `d := Cfg.ofWords …`, supplies `rfl` for the state, and proves the relative-window premise by simplifying `Cfg.ofWords`. Its cut is exactly `h.2.1`; its final equality is `h.1.trans` followed by configuration extensionality.

| Canonical row | Witness and budget | Finish-identification obligation actually discharged |
|---|---|---|
| `transferTM_run` | `2n+2 ≤ 3n+3`, since the difference is `n+1 ≥ 0` | Source becomes `[]`; destination becomes the old source word. `hne` separates the two updates. `hdst` makes the destination exterior blank, including any potential old suffix. |
| `copyTM_run` | `2n+2 ≤ 3n+3` | Destination becomes the source word and the source stays unchanged. The proof explicitly uses `hdst` outside the overwritten interval. |
| `clearTM_run` | `2n+2 ≤ 2n+2` | Erased interior and the old buffer's blank exterior together equal the globally blank buffer. |
| `incrementTM_run_succ` | `2p+2 ≤ 2n+2`, using `List.takeWhile_sublist` | The proof derives `v.length=n` from the existing split/value lemmas, so the retained exterior is exactly the new buffer's blank exterior. |
| `incrementTM_run_overflow` | `2n+2 ≤ 2n+2` | `replicate n false` has length `n`; the retained exterior agrees with its buffer. |

This is the requested proof dependency direction: generalized trace → framed contract → canonical run row. None of the five canonical run proofs reconstructs its own machine trace.

**The four space rows.** Transfer, copy, clear, and increment all specialize their generalized trace at `Cfg.ofWords`, for unrestricted elapsed time. They reuse the unchanged `catalog_space_bound` and `catalog_space_one`. From the trace, at every time `u` an active canonical head lies in `[-1,m]`, including the stationary tail, so

\[
\begin{aligned}
\{\text{head}(u):0\le u\le t\}&\subseteq\{-1,0,\ldots,m\},\\
\texttt{spaceUsedByTape}(t)&\le m-(-1)+1=m+2.
\end{aligned}
\]

For transfer/copy/clear, `m=n`. For increment, the split supplies `p≤n`, hence `spaceUsedByTape(t)≤p+2≤n+2`. An inactive head stays at zero; `Finset.range (t+1)` is nonempty even at `t=0`, so its visited set is exactly `{0}` and its cardinality is 1. Thus neither a missing post-exit argument nor a zero-time counting defect occurs. Keeping the unused canonical `hdst` premise in the two space signatures respects the freeze; it is not needed for head containment.

**Freeze, reordering, and evidence.** Reverse-applying the attached patch to the final source succeeds without repair; reapplying it returns the final bytes exactly. The reconstructed source identifiers are:

| Version | Git blob | SHA-256 |
|---|---|---|
| Before | `1472162d3a58b39123e3971b8555dbf6d113dec8` | `155177f67e059cb50ac392aee0081888f629a8def43aeee950f3f51401b7d48f` |
| After | `8d8cb704798f02af6014f8f27fa05075930c5521` | `2f28360cdb77235f8a1a732f084f032824ac5f12adf773f6b8ee6874ea5506e3` |

The after hash equals the agent's reported delivery hash. The patch names only `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` and contains no C/shim file. Independent declaration extraction found:

- 44 public declarations before and after, with all signatures and all 44 attached docstrings byte-identical; exactly the authorized five framed, five canonical, and four space proof bodies changed. The other 30 public declarations are unchanged in full.
- 384 private declarations before and after: remove `catalog_erase_take`, add `catalogTape`, change exactly the 14 listed privates, and leave the other 369 common private declarations and their docstrings unchanged.
- `catalogCfg`, `catalogTrace`, `catalog_trace_run`, and all compare declarations unchanged. All imports and the relative order of all surviving declarations other than the five moved framed contracts are unchanged.
- The existing framed section now precedes the canonical rows, enabling their citations. Its statements and public docstrings moved without edits. Comment-stripped admissions fall from exactly five to zero.

The supplied axiom probe/log covers the exact 44-name explicit public inventory: seven definitions/inductives have no axioms and 37 declarations list only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` occurs. The maintainer's integration log reports Catalog exit 0 with no own admissions, Zone with its two baseline admissions, Codes2Tape with its one baseline admission, and the facade exit 0. Its lint log reports 0 FAIL and four size warnings over 12 files; the agent's earlier report was over 11 files. These are separate snapshots, not an unexplained source change in this patch. The original ZIP/checksum manifest, agent's 325-generated-constant probe, and complete repository/toolchain are not attached, so those broader execution/integrity claims remain attestations.

**Duplication ruling.** The attached amended TEMPLATE makes accounting corrections within an acknowledged family minor unless the approval's scope changes: another file crosses the threshold, copies lie outside the named family, or the named resolution cannot work. None applies here. Every new directed pair is between the named Catalog sibling rows or their traces/configurations. The authoritative plan's 12.2c item 5 explicitly schedules those rows for a common scanner, and the fill introduces no further affected file. The new wrappers and generalized invariants fit that resolution. Consequently F1–F2 are minors, not debt majors. This ruling does not turn unchanged census counts into a claim of no repeated proof text.

The six reported census totals agree between the agent's before/after comparison and the maintainer's after log:

| File | Before | After |
|---|---:|---:|
| Composition | 6/19 | 6/19 |
| Primitives | 173/272 | 173/272 |
| TimeConstructible | 20/21 | 20/21 |
| Loop | 98/199 | 98/199 |
| Wrappers | 19/29 | 19/29 |
| Catalog | 318/428 | 318/428 |

The standing rule excludes in-file near-matches from membership, while recording them separately. Thus these totals can remain fixed while the sibling proof text changes. The historical ledger still quotes Catalog's older denominator 423; the fill's comparison correctly uses 428 on **both** sides. No claim of five declarations added by this fill is warranted. The full six-file generator cannot be rerun from this packet because its script and five source files are absent.

For the supplementary text screen, I independently extracted bodies, removed comments/whitespace, and reconstructed greedy matching with tiles of at least 25 characters, a 60-character floor, the one-half source-coverage threshold, and the proof/term kind guard. I screened every pair involving a changed/added/removed declaration against all declarations in the supplied Catalog versions; the unchanged pairs were retained from the supplied logs, with their source bytes protected by the independent freeze. All affected-pair numerators and denominators reproduce the logs exactly, with no additional qualifying pair found. This is an independent delta reconstruction, not execution of the unavailable original script.

The arithmetic is:

\[
\begin{aligned}
\text{pairs after}&=276-20+16=272,\\
\text{matched characters after}
&=98{,}775-7{,}265+5{,}520+1{,}415\\
&=98{,}445,\\
\text{net character change}&=-330.
\end{aligned}
\]

The `+1,415` comes from changes to persistent pairs. There are 23 such changes; the two omitted from the diff alter only denominators. Pairwise matched-character totals count directed comparisons, not unique source bytes.

**Could more have been shared within single-file ownership? Yes.** The batch already owns the affected private traces, and the three sweep contracts perform the same extraction of final state, earlier-exit exclusion, and head interval from `catalogTrace`. One private consequence lemma, parameterized by the active tapes, their initial positions, final tape transformation, and phase equations, could discharge those three common conclusions once. The machine-specific forward/turn/return facts would remain its inputs. This needs no import or public-statement change; it could replace repeated body fragments within the permitted private section. A deeper common scanner can additionally factor the transition/invariant family in 12.2c. Thus ownership did not force all the new repetition, but the scheduled resolution remains feasible and covers it.

**Notation.** `d` is the initial configuration; `w` is the relevant word; `n=w.length`; `p` is the initial true-prefix length on successful increment, or the existing split length when discussing the shared increment trace; `m` is the forward-pass length (`n`, or `p` on success); `t,u` are elapsed times; `r` is the trace's return index; `rest` is the suffix after the first false bit; `v` is the successful increment result. Other identifiers retain their meanings in the quoted Lean declarations. Tape-update intervals are half-open; containment intervals are inclusive.
