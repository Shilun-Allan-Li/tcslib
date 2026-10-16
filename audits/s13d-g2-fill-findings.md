# External audit findings — §13d G2 fill gate

**Verdict: PASS — 0 blockers / 0 majors / 3 minors.** The supplied changes preserve the public statements and satisfy ruling 7. Re-pointing `zoneCascadeRight_zero` at the shared unfolding lemma is acceptable. The clear-row consequence proof is residual duplication, but it lies within the explicitly acknowledged §12.6 sibling family; the accounting-minor rule applies. The three minors below should be corrected or explicitly dispositioned in the resolutions.

This is an audit of the attached sources and evidence. **I could not run Lean:** a local Lean 4.25.0 executable failed even on `--version`, with `error: failed to locate application`. All elaboration, axiom-print and downstream-replay results below are supplied evidence, not fresh kernel checks by this auditor.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Build/Catalog.lean` · `clearTM_run_ofCfg`, `catalog_trace_clauses`; plan §4d item 5 and §4e | The clear row retains a complete specialization of the new generic consequence argument. This is debt under failure mode 5, within an already acknowledged family. | The second conjunct of `clearTM_run_ofCfg` independently derives exactly the earlier-exit and head-envelope conclusions obtained from `catalog_trace_clauses` with `touched := (· = i)` and `catalog_clear_trace`. Its body is unchanged by #108. The attached plan explicitly includes the §12.6 framed consequence proofs in acknowledged item 5 and specifically schedules one private consequence lemma for the three sweep contracts. Thus this is neither an undisclosed new family nor covered merely by the three new-pair approvals. | Prefer replacing the two inline clauses by the shared helper, keeping the endpoint proof and statement unchanged. Until that repair, record this precise residual under item 5, with its disposition/window; do not describe that factoring as fully discharged. No new debt acknowledgment is needed for this within-scope accounting correction. |
| 2 | minor | `audits/evidence/s13d/g2-fill/NOTES.md` §3 | The per-file in-file overlap subtotals are inaccurate. | Re-running the exact v3 screens gives **105,568 → 98,150** for `Build/Catalog.lean`, **240 → 240** separately for `Build/Contract/Catalog.lean`, and **3,840 → 2,844** for `Build/Zone.lean`. The stated Catalog figures, 105,808 → 98,390, aggregate both Catalog files; the stated final Zone figure, 2,884, is 40 too high. The global totals and all three approved pairs are correct. | Record the full paths and corrected subtotals. Label these as directed overlap sums, not unique copied-source sizes. This changes no approved family or disposition. |
| 3 | minor | `Build/Catalog.lean` · sketches of `copyMapTM_run_ofCfg` and `transferMapTM_run_ofCfg`; `NOTES.md` §1 | Some inherited sketch wording still describes the pre-fill organization. | The copy sketch names `catalog_write_take` for the prefix step, but neither its proof nor `catalog_transferMap_trace` calls that lemma: the mapped trace proves the value-parametric update inline. The transfer sketch begins with “The mapped copy's trace,” whereas the actual dependency is transfer trace → transfer row → copy row. The later “Formally” sentence correctly describes the copy. Also, “the mapped framed block … moves verbatim” is only accurate for the two `_plain` declaration blocks: the two target proofs change and transfer is moved ahead of copy. | Describe `catalog_transferMap_trace` as the shared trace, the inline mapped-prefix update, and the copy as its identity-residue consequence. Qualify the movement claim: statements preserved; `_plain` blocks byte-identical; target proofs filled and ordered by dependency. |

## Packet integrity and freeze — brief item 1

The uploaded `s13d-g2-fill-bundle.md` has SHA-256

`f6044d478f76b73df94e7a08016c9b7bb5e2f1dd0ee945d26dba0f4dd5edcfc7`

and exactly **60 distinct section paths**. Every listed category in the pack is present. Removing the bundle headers, outer code fences where present, and separator padding reproduces **all 38 entries** in the embedded `SHA256SUMS`. The v3 screen also matches its separately recorded hash, `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`.

I applied `gate/pr108.patch` to isolated copies of the two attached base files. Both outputs equal the supplied head files byte for byte. Independently, running `mkoverlay.py` with its mapped block and `mkzone.py` on those bases reproduces the same two head files exactly. The Git blob identifiers agree with the patch:

| File | Base blob | Head blob |
|---|---|---|
| `Build/Catalog.lean` | `398405d2cd58838e40533394ed1d237dca7a5bda` | `f283a93e6cd4b25b962d825c7c2693db64f19e2b` |
| `Build/Zone.lean` | `99a65f10f4ab43c5eaf852e2c01852e8f367afe9` | `1ccc16caacd49d743275b5b358fce42df97207b0` |

The supplied freeze script reproduces both freeze logs exactly. An additional comment-aware comparison checks the actual public header text, including binders, rather than only whitespace-normalized statements. The inline-attributed `ZoneContents.swap_swap` is also unchanged. **All 160 explicit public statements are byte-identical.** Imports and options are unchanged.

| File | Public declarations | Private declarations | Source lines |
|---|---:|---:|---:|
| Catalog | 95 → 95 | 391 → 392 | 12,874 → 12,977 |
| Zone | 65 → 65 | 8 → 12 | 1,324 → 1,388 |

Exactly these public proof bodies change:

- Catalog: `copyMapTM_run_ofCfg`, `transferMapTM_run_ofCfg`, `copyTM_run_ofCfg`, `transferTM_run_ofCfg`, `copyTM_spaceUsedByTape`, `transferTM_spaceUsedByTape`.
- Zone: `zoneCascadeRight_home`, `zoneSide_cascadeRight`, `zoneCascadeRight_lengths`, `zoneCascadeRight_zero`.

Catalog removes exactly `catalogCopyF`, `catalogCopyR`, `catalogTransferR`, `catalog_copy_forward`, `catalog_copy_trace`, and `catalog_transfer_trace`. It adds exactly `catalogSweepF`, `catalogSweepR`, `catalogSweepResidueR`, `catalog_transferMap_trace`, `catalog_trace_clauses`, `copyMapTM_step_eq`, and `copyMapTM_runFrom_eq`. Zone adds exactly `zoneCascadeRight_zero_eq`, `zoneStepPair_below`, `zoneStepPair_pre`, and `zoneCascadeRight_classical`. No retained private declaration changes. The two `_plain` declarations are byte-identical and move before the plain framed rows.

## Shared trace and copy-as-transfer — brief items 2–3

The three new definitions have the following meanings, checked against their bodies and docstrings:

| Definition | Meaning |
|---|---|
| `catalogSweepF` | Starting from `d`, enter `sweep`, replace only the destination prefix of length `r` by `v`, and advance the selected heads by `r`. Preserve every other field. |
| `catalogSweepR` | Keep the full destination overwrite of length `L`, enter `rewind`, and put the selected heads at offset `r - 1`. |
| `catalogSweepResidueR` | Additionally overwrite the crossed source suffix, from offset `r` through `L - 1`, by `u`. This source overwrite has priority in the raw definition; the run theorem requires distinct source and destination tapes. |

In `catalog_transferMap_trace`, the destination value at offset `r` is precisely the merge of **the original destination cell** and `extract w[r]`. The return residue is computed from the original source word. A return configuration indexed by `r + 1` has rewritten only the suffix starting at `r + 1`; the cell read at offset `r` remains original. Thus even a residue that writes blanks cannot prematurely stop the return pass.

For `L = w.length`, the trace is

\[
\text{run}(t)=
\begin{cases}
F(t),&t\le L,\\
R(2L+1-t),&L<t\le 2L+1,\\
D,&t\ge 2L+2.
\end{cases}
\]

The shared public `catalog_trace_run` supplies this trace from the local transitions. The selected head offsets are respectively `t`, `2L - t`, and `0`; hence they lie in `[-1,L]`. The forward and return states differ from `done`, and the exit first occurs at `2L+2`. `catalog_trace_clauses` extracts these consequences without another machine trace proof.

**Ruling 7 is satisfied.** `transferMapTM_run_ofCfg` consumes this one mapped trace; `copyMapTM_run_ofCfg` consumes the proved transfer row. The two plain framed rows instantiate the mapped rows with `extract := id`, `merge := fun _ s => s`, and blank residue for transfer. The two plain space lemmas use the same mapped trace, with blank residue for transfer and `some` for copy; the trace's stationary tail justifies their bounds at arbitrary times.

**The copy-as-transfer claim is correct.** The only potentially different action is a nonblank return step. If the scanned cell is `some b`, transfer with `rest := some` writes `some b` back to that same cell. `Function.update_eq_self` makes its effect equal to the copy's no-write action. All other transitions agree. This step equality even allows `src = dst`; the framed run theorem separately and correctly requires `src ≠ dst`. Iterating equal step functions gives `copyMapTM_runFrom_eq`. The endpoint normalization uses

\[
\texttt{none.bind some}=\texttt{none},\qquad
\texttt{(some b).bind some}=\texttt{some b}.
\]

The base source retains the original proved plain traces while the mapped rows are admitted. The final source proves the mapped transfer before deriving copy and then the plain rows. The final supplied axiom walks contain no `sorryAx`. These establish the required dependency property for the attached base and head; intermediate Git trees are not attached.

## Zone and the regression — brief item 4

`zoneSide_cascadeRight` and `zoneCascadeRight_home` are exactly the first and second projections of `zoneCascadeRight_classical`. Its successor case obtains the lower classical pre-state from `zoneStepPair_pre`, which uses `zoneStepPair_below` for the lower frame and left half-size. Nonemptiness follows because the incoming prefix has length `min (2^j) donor.length > 0`. The lower room calculation is

\[
2^j+2^{j-1}\le 2^j+2^j=2\cdot2^j=\texttt{zoneCapacity }j,
\]

where subtraction is natural-number subtraction, including at `j = 0`. The two surrounding step pairs preserve the side concatenations; home preservation is definitional, as the supplied seam probe also records. No half-full restoration theorem is used to obtain the new home.

**Explicit regression ruling: acceptable.** `zoneCascadeRight_zero_eq` still checks the actual definition: both folds over `List.range 0` reduce away, so `show zoneMove true z = _` is a definitional reduction, followed by the two guard hypotheses. It does not appeal to `zoneCascadeRight_classical` or either public cascade conclusion. The unchanged regression then applies this equality and `zoneSide_moveRight`. Sharing this unfolding proof does not make the regression circular or detach it from the cascade definition. No separate re-expansion of the folds is required.

`zoneCascadeRight_lengths` also uses the shared zero-case and below-level facts, with its stronger donor-size hypothesis preserved.

## Duplication accounting and debt ruling — brief item 5

Both complete v3 runs reproduce **every output line** of the corresponding supplied screen, after removing their descriptive header. The population is exactly the five G2–G4 files plus `Simulation.lean`; the two Catalog paths remain distinct.

| Measurement | Base | Head |
|---|---:|---:|
| Screened declarations | 548 | 554 |
| Directed pairs | 384 | 369 |
| Reported overlap characters | 124,738 | 116,324 |

There are exactly **3 new-by-name pairs, 18 removed pairs, and no new cross-file pair**. The character reconciliation is

\[
1{,}462-9{,}246-630=-8{,}414
=116{,}324-124{,}738,
\]

where the three terms are new-pair text, removed-pair text, and the net change among retained pairs. These directed overlap sums can count the same source material repeatedly; they are not a unique-source census or a copied-code fraction.

| New pair: target ← source | Exact overlap | Successor check and disposition |
|---|---:|---|
| `catalog_transferMap_trace` ← `catalog_clear_trace` | 1,086 / 1,617 = 67% rounded | The base pair is `catalog_transfer_trace` ← `catalog_clear_trace`, 866 / 1,617 = 54%. Source-preservation checks, transition extensionality, delimiter cases and arithmetic are the same sweep-proof idiom. The new mapped trace succeeds the removed transfer trace. Approved by the user on 2026-10-15. |
| `catalog_transferMap_trace` ← `catalog_write_take` | 62 / 124 = 50% | Exactly the two reported 31-character fragments. New by name; not a claim that the mapped trace calls this lemma. Approved by the user on 2026-10-15. |
| `zoneCascadeRight_lengths` ← `zoneStepPair_below` | 314 / 582 = 54% rounded | The base pair is `zoneCascadeRight_lengths` ← `zoneSide_cascadeRight`, 761 / 1,444 = 53%. The helper extracts the old descending pre-state calculation; the remaining overlap includes the active-pair call and frame rewrites, including the ascending configuration in the lengths proof. Approved by the user on 2026-10-15. |

The supplied segment listings for the three new pairs match independent extraction. The base's 91% pair (`catalog_transfer_trace` ← `catalog_copy_trace`, 1,169 / 1,290) is gone. Its 80% zero-case pair is also gone. No claim is made that every retained space-wrapper or sibling overlap has disappeared.

The corrected cumulative in-file totals are:

| File | Base | Head |
|---|---:|---:|
| `Build/Catalog.lean` | 105,568 | 98,150 |
| `Build/Contract/Catalog.lean` | 240 | 240 |
| `Build/Zone.lean` | 3,840 | 2,844 |
| `Build/ZoneTape.lean` | 1,440 | 1,440 |
| `Build/ZoneRebalance.lean` | 0 | 0 |
| `Simulation.lean` | 4,318 | 4,318 |
| Cross-file directed overlaps | 9,332 | 9,332 |
| **Total** | **124,738** | **116,324** |

**Explicit maintainer-observation ruling: yes, the inline clear clauses are residual debt.** Instantiate `catalog_trace_clauses` with `catalogClearF i d`, `catalogClearR i d w.length`, the exact exit configuration in `catalog_clear_trace`, and `touched j := j = i`. The trace premise is `catalog_clear_trace`; all three state/head premises are definitional. The helper's result is exactly the conjunction independently proved after the endpoint in `clearTM_run_ofCfg`.

**Severity is minor, not a new major.** The attached plan §4d item 5 explicitly names these framed consequence proofs and this proposed shared consequence lemma. Its 2026-10-10 decision-log records describe the family as acknowledged and apply the accounting-minor rule; the prior G2–G4 findings preserve that existing trace debt. Nothing here adds a file outside that scope, establishes a new threshold crossing, or makes the scheduled factoring impossible. The three 2026-10-15 pair approvals do not themselves acknowledge this fourth semantic overlap; the earlier, broader record is the applicable authority. Finding 1 keeps the residual visible instead of declaring it paid off.

## Documentation, downstream and records — brief items 6–8

All eleven new privates have docstrings. The nontrivial new proofs have sketches; the short run-equality and zero-unfolding lemmas explain their reductions directly. The five added/extended sketches otherwise describe the actual identity instantiations and shared induction. Zone's “proved” status and the G2 section's one-trace statement agree with the source and supplied axiom output. Finding 3 covers the remaining stale references.

`copyMapTM_contract` and `transferMapTM_contract` continue to use `sweepContract` with the two now-proved framed rows. Their preconditions, endpoints and trajectory fields are unchanged. The supplied base already contains MIG-1 S's two `Cfg.ofWords_*_endpoint` lemmas, which survive unchanged; the migration-stage content prerequisite is present.

**Obligation 4:** in the attached current Lean sources, no file outside `Build/Catalog.lean` unfolds any of the four copy/transfer tables by name. `Build/Contract/Catalog.lean` mentions the mapped machine constants in contract types and cites their framed theorems. Within Catalog, explicit table unfolding occurs only in `catalog_transferMap_trace` and `copyMapTM_step_eq`; identity specialization uses definitions or the `_plain` equalities. This verifies the supplied scope. The pack's full-repository search remains an attestation because the full tree, including F-D consumers, is not included.

The backlog's RD-5 “Next” entry correctly records the fill as landed but awaiting this gate, and keeps G4's host work and G5 obligations separate. Nothing here closes the two G4 witness admissions or the statement gate's G5-carried minors. The two filled Catalog targets and the Zone target are the only removed admissions in the supplied base/head sources.

Adversarial boundary checks against the literal interfaces:

- **Empty word:** time is `2·0+2 = 2`; the right-blank turn moves the selected heads to offset `-1`, and the left-blank entry restores offset `0`. Both overwritten intervals are empty, so all tape cells are unchanged.
- **Arbitrary frames and blank residues:** displaced integer heads and nonblank destination/frame cells are permitted. Forward merging uses the original destination cell; return writes occur behind the next source read. The theorem does not require injective extraction or nonblank residues.
- **Aliased tapes:** the copy/identity-residue step equality still holds, but the framed guarantees require `src ≠ dst`. No use silently drops that hypothesis.
- **Small donor:** with two levels, index `1`, a full lower-left zone, empty lower-right zone, empty upper-left zone and a one-cell upper-right donor, the home theorem applies. It does not borrow the stronger `2^j` donor-size requirement of `zoneCascadeRight_lengths`.
- **Stored virtual blank:** a donor `[none]` is nonempty and legitimately moves `none` into home. This is distinct from an absent donor `[]`; `headI` does not trivialize the theorem.

These are mathematical/source checks, not separately executed Lean tests.

## Evidence checked and limits

Independently executed: bundle/inventory and embedded-hash verification; patch application and both generators; both freeze checks plus raw-header comparison; both full six-file copy screens, delta accounting and new-pair segment extraction; both two-file style-lint runs; warning-log comparison; public-name/axiom-log reconciliation; patch hygiene and width checks; replay-order/log reconciliation.

The supplied logs are internally consistent with the checked sources:

| Supplied evidence | Checked result |
|---|---|
| Catalog elaboration/axiom output | 95 distinct explicit-public entries, exactly the generated probe inventory. Axiom sets: 30 empty; 8 `{propext}`; 6 `{propext, Quot.sound}`; 51 the standard triple. No error or `sorryAx` entry. Warnings 92 → 78, with zero new and 14 removed. |
| Zone elaboration/axiom output | 65 distinct explicit-public entries, exactly the generated probe inventory. Axiom sets: 2 empty; 17 `{propext}`; 19 `{propext, Quot.sound}`; 27 the standard triple. No errors or `sorryAx`; its one base sorry warning disappears. |
| Replay at recorded head `a9ee4701` | Exactly 87 distinct module rows, in the attached replay order; every exit and error count is zero. Catalog and Zone each report zero sorries. Other modules retain reported admissions, including the two G4 witnesses. |
| Lint | Fresh file-style runs reproduce 50 → 49 findings, with no new finding. The supplied campaign logs have zero FAIL; WARN sets agree apart from the two file-size counts. Existing style warnings are not claimed to be absent. |
| Hygiene and widths | Exactly 496 added patch lines; no supplied forbidden-token pattern occurs, and no added line exceeds 100 characters. |
| Import/seam probes | The input contains 52 `#check`s and three seam examples; the attached outputs report success/no errors. These probes were not re-elaborated here. |

Limits: I did not fetch GitHub or independently authenticate the commit ancestry, the first intermediate commit `8e3cee48`, or merge `b6e0344c` against remote Git objects. The file-level reconstruction is exact; those historical identities remain supplied provenance. The packet lacks the complete dependency/olean snapshot and the earlier full 87-module replay, so “the other 85 sorry counts are unchanged” and “this is the entire downstream closure” remain attestations, not independently reproduced comparisons. The replay wrapper delegates freshness to `lean_check_tree.sh`, which is not attached. Likewise, exclusive historical use of throttled Lean and isolated Python cannot be established from the resulting logs alone. None of the independent Python/text checks substitutes for Lean elaboration.

This fill audit preserves the closed statement gate's source-fidelity rulings; it is not a fresh audit of the full Hennie–Stearns construction or a claim that G4/G5 are complete.

## Notation

`d` is the starting configuration; `w` is its delimited source word; `L = w.length`; `r` is a sweep index; `t` is elapsed time; `run(t)` is the mapped transfer's configuration at time `t`; `F`, `R`, and `D` are the forward family, return family, and exit configuration in `catalogTrace`; `v` and `u` are destination and residue value functions; `b` is a scanned symbol. `i` is the cleared tape; `j` denotes a zone level in the Zone calculation and a tape index in the clear-helper instantiation. The standard axiom triple is `{propext, Classical.choice, Quot.sound}`. An arrow `target ← source` identifies a directed pair in the supplied text screen.
