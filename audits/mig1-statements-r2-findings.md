Input SHA-256: `6acaad71a9bea8fb60a1b9008a41634cb079392f7df77021b24bac6d7bce1bd0`.

Exactly **115** `## ===== <path> =====` sections. Both match the commissioned values.

**Verdict: gate closes — 0 blockers, 0 majors, 3 minors.** Round 1's major is repaired: the surviving preparation lemma supplies the fuel-head clause, and the full-file overlay derives the extended contract and public budget from the surviving home declarations. I found no false changed statement, changed machine definition, or additional unsatisfied retarget in the planned migration. The remaining findings concern the precision and enforcement of evidence claims.

This audit concerns the supplied packet at measurement base `99ad2f9894121f45c79a27722d9466223be16473`. I independently rebuilt the source artifacts and ran the applicable Python/shell checks. Lean is not on this workspace's PATH, and the attested olean snapshot and complete repository are not supplied; I therefore assess elaboration and kernel-axiom claims as supplied execution evidence, not as independently rerun Lean checks. I used no repository-history access and did not modify the input bundle. References below use extracted file line numbers, excluding the bundle's Markdown fences; `r2/` means `audits/evidence/mig1/gate/r2/`.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | minor | `r2/scripts/runall.sh:25–50, 92–97` · input precheck; pack · finding 2 | The assertion that every missing input causes exit 2 before anything is written is broader than the implemented precheck. | The precheck lists gate inputs but omits the worktree source files read by `build_unit.py`, including `Build/Loop.lean` and the H2 draft. In an isolated fixture, with all listed inputs present but `Build/Loop.lean` absent, the unchanged runner created its output directories and log, recorded two builder failures, and exited **1** at the concatenation of missing outputs. The elaborator was never reached. By contrast, removing `data/consumer-names.json` produced the advertised exit **2**, with no output directories. | Check the required source paths before `mkdir` and log truncation, and include a missing-source control; alternatively narrow the stated guarantee to the explicitly listed gate inputs. The builder itself correctly refuses the missing source without replacing its output. |
| R2-2 | minor | `r2/scripts/overlaycheck.py:77–88`; `r2/scripts/runall.sh:335–344` · retarget negative control | The runner verifies the set of failing examples, but does not enforce the claimed **exactly two errors** or the tip control's exit status. | `set(where) == names` discards error multiplicities. Appending one duplicate of the supplied preparation-error diagnostic to the supplied tip diagnostics produced `tip file errors: 3, by restated copy: {'f2_loopHost_prepare': 2, 'f2_loopHost_contracts': 1}` followed by **`RESULT: PASS`**, exit 0. The runner records `tipstat` without comparing it against an expectation. The actual supplied run nevertheless reports exactly two errors and exit 1. | Require one error in each expected example, no others, and check the expected nonzero elaborator exit status. Add this duplicate-diagnostic control. This is a checker-strength defect, not a contradiction of the recorded successful repair. |
| R2-3 | minor | Round-2 pack · “Accessibility”; `r2/data/retarget-table.tsv` · six `f2_head_steps` retargets | “174 citations are accessible now” obscures the prerequisite for the six citations awaiting MIG-0b's interval theorem. | All six head-bound citations are labelled `accessible = yes`, although the target home is explicitly `Finite (MIG-0b)`. The pack and stand-in documentation state that this theorem is absent at the measurement tip; the overlay uses a stand-in for that reason. Within the 174 planned-access entries, **6 additionally require MIG-0b** and **168 require no such additional import/landing prerequisite beyond their prescribed moves and repairs**; the other categories remain **3 after F-A** and **38 not carried**. | Describe this as accessibility of the planned destinations, conditional on the moves/repairs and MIG-0b, and record the six MIG-0b prerequisites as explicitly as the three F-A prerequisites. The binding order already supplies them, so this does not reopen the deletion-plan major. |

The following rows explicitly record the areas with **no findings**. They are scoped conclusions, not a certification of an unperformed landing replay.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| N1 | note — no findings | `LoopOverlay.lean.txt` · `loopHost_prepare` | Round-1 finding 1's missing fuel-head clause is repaired for both forwarding modes. | The new conjunct concerns the actual fuel configuration `F.tm.runFrom (F.tm.initCfg x) u`, with `u ≤ T x.length`; the extended contract consumes it as `hfuel`. The emitting caller discards the extra conjunct. | None. |
| N2 | note — no findings | Overlay · extended contract, four moved budget lemmas, stand-in | The seven reviewed statements are true as stated and have the intended meanings. | Literal-type restatements and mathematical arguments appear below. The stand-in reproduces MIG-0b's statement and proof after the disclosed declaration-name, visibility and namespace change. | Drop the stand-in and use the actual MIG-0b theorem at landing, as planned. |
| N3 | note — no findings | Overlay · part 1, part 2 and three diffs | The overlay implements precisely the disclosed source changes. | Rebuilding gives the exact supplied 5,743-line overlay. Each supplied diff applies cleanly and produces the corresponding generated artifact exactly. Part 1 has only two changed private statements, five added private declarations, and three changed public proof bodies; machine definitions and public row types are unchanged. | Retain the separate F-C landing compile/replay obligation. |
| N4 | note — no findings | Retarget population and replacement proofs | No additional weaker or inaccessible retarget was found under the stated landing order. | 59 declarations and 215 dependency entries reproduce; all private retargets are in the receiving home. The seven discarded proofs are replaced without importing their Catalog-region dependencies. See R2-3 for the timing qualification. | None to the planned retargets. |
| N5 | note — no findings | Deletion inventory and decisions 1–5 | The repaired inventory and proof-staging decisions are coherent. | Both deletion tables reproduce byte for byte; exactly two rows differ. The counts remain 378 declarations and 9,172 docstring-inclusive lines, with no unassigned fate. Decision 2's dependency scan reproduces, and excluding H2's head lemma gives 70 MIG-1 landing names. | Recheck names, closures and line positions at S's actual base. |
| N6 | note — no findings | Builder, bundle manifests, corrected descriptions | Round-1 findings 3–4 are repaired; the builder portion of finding 2 is repaired. | All 115 manifest paths are present, with no extra or duplicate section. The evidence map supplies 45 round-2 records and 36 reused inputs. All six builder refusal controls leave a sentinel output untouched. The three corrected descriptions agree with their evidence. | None beyond R2-1–R2-2's narrower runner issues. |
| N7 | note — no findings | Unchanged unit, probes, identities, R3 sites and consumer delta | The packet supports preservation of the round-1 statement surface and the stated measured deltas. | Unit, spec tail and bridge rebuild byte for byte; 158 identities pass; the three identity mutations fail exactly as expected. All 24 R3 checks pass at the measurement base. The consumer JSON differs only by the three disclosed comment mentions. | Treat later campaign-tip measurements separately. |
| N8 | note — no findings | Migration sequencing and temporary duplication | The repair supplies the dependency missing from the acknowledged deletion plan. | The stand-in is evidence-only; the existing acknowledged copy family still retires at F-D. F-C now strengthens preparation before replacing the contract and using the budget. No further copied-material family or unresolvable scheduled deletion was identified. | Follow the recorded sequencing and final duplication screen. |

I extracted the seven types with comments removed and compared the following restatements with their docstrings and source counterparts.

| Declaration · overlay line | Literal meaning and justification |
|---|---|
| `mig0bStandIn_workTapePos_runFrom_mem_Icc:1247` | For any machine, starting configuration, tape and natural number of steps, that tape's final head is between its starting position minus the step count and its starting position plus the step count. The supplied one-step displacement theorem gives both inequalities for one transition, and induction gives the result for any number of transitions. Halted configurations are stationary, so no liveness assumption is needed; neither finite state types nor inhabited tape-index types are required. |
| `loopHost_prepare:1272` | If the fuel machine computes the binary representation of `R` within `T`, preparation reaches `loopReady` within `5T+7`, retaining a halted fuel configuration with that output and every fuel head in `[-T,T]`, for either `forward` and either `findMode`. Choose the first fuel halt `u ≤ T` and the actual run configuration there; the existing capture/setup/rewind construction yields the required host endpoint. The interval theorem at the initialized fuel configuration yields the additional head clause. The added clause concerns the fuel run and does not depend on forwarding. |
| `loopCall_heads:2083` | A canonical call built from a canonical body configuration and a fuel configuration whose heads are in `[-B,B]` has every host work head in that same interval. In the tape-bank decomposition, the body, flag, counter and capture heads are zero, and the remaining heads are exactly the supplied fuel heads. Since `B` is natural, zero satisfies the bound; no restriction on the stored word's length is required. |
| `loopHost_contracts:2142` | Under the fuel, invariant, startup and first-return-or-halt hypotheses, the concrete host has an initialized seam family through candidate `R`, startup and local segments bounded by `10(T+1)`, the stated acceptance/exhaustion outputs, candidate heads bounded by `T`, and a halted exhaustion terminal bounded by `T+10(T+1)`. Canonical seams retain the single bounded fuel residue and reset the other heads; the local phase contracts provide each segment, including seams after an earlier acceptance. For a rejecting last candidate the terminal is its actual segment endpoint; for an accepting last candidate it is a halted copy of the next canonical candidate, which need not be reached. The source proof chooses `loopHost_bound = 10`, so exposing that coefficient preserves a proved construction rather than inferring a particular value from an arbitrary existential. |
| `segment_heads:2329` | A finite family of `N` seams, each nonterminal seam bounded by `H`, with a halted terminal bounded by `H+B`, and each local segment reaching either a halt or the next seam within `B`, confines the entire run from seam zero to `[-(H+B),H+B]`. Induct on `N`: within the first segment use displacement at most its duration; after its endpoint use either halt absorption or the induction hypothesis on the shifted seam family. At `N=0`, seam zero is already the bounded halted terminal. Zero-duration segments cause no problem because the induction decreases the number of remaining seams. |
| `space_radius:2369` | If every initialized head position at every time lies in `[-B,B]`, total visited work-tape space at any prefix is at most `M.k·(2B+1)`. Each tape's visited-position set is contained in that integer interval, whose cardinality is `2B+1`. Summing its cardinality bound over the work tapes gives the conclusion, including the origin at time zero. |
| `seamed_space:2389` | An initialized run reaching seam zero within `B` steps, followed by the preceding seam/terminal/segment conditions, uses at most `M.k·(2(H+B)+1)` space at every time. Before startup, a head starting at zero has magnitude at most the elapsed time, hence at most `B ≤ H+B`. After startup, run concatenation and `segment_heads` supply the same radius. `space_radius` converts this all-time bound to space. |

The preparation repair can be checked directly from the witness rather than from the old weaker existential conclusion. With the source proof's choices,

\[
1\le u\le T(|x|),\qquad
c=F.\mathrm{tm}.\mathrm{runFrom}(F.\mathrm{tm}.\mathrm{initCfg}(x),u).
\]

The initial work heads are zero, so for every fuel tape `i`,

\[
-T(|x|)\le -u
\le c.\mathrm{workTapePos}(i)
\le u\le T(|x|).
\]

The halted configuration agrees with the fuel run at the promised time, so its output is `Nat.bits (R x.length)`. For preparation's input-rewind duration `v`, the existing contracts give

\[
\begin{aligned}
|c.\mathrm{output}|&\le T(|x|),\\
v&\le c.\mathrm{inputPos}.\mathrm{val}+2\le u+3,\\
u+3|c.\mathrm{output}|+4+v
&\le 2u+3T(|x|)+7
\le 5T(|x|)+7.
\end{aligned}
\]

Both forwarding modes retain this same argument. In the moved contract, the candidate-head bound is obtained by applying `loopCall_heads` to this very `hfuel`; it is not assumed through a probe shim.

The explicit coefficient and budget calculations are also valid literally:

\[
\mathrm{loopHost\_bound}
=\max(1,\max(9,3+2+5))=10,
\]

\[
\begin{aligned}
\mathrm{startup}&\le (5T(|x|)+7)+(T(|x|)+2)
=6T(|x|)+9\le10(T(|x|)+1),\\
3t+2|\mathrm{word}|+5
&\le5T(|x|)+5\le10(T(|x|)+1)
\quad(t,|\mathrm{word}|\le T(|x|)),\\
2\bigl(T(|x|)+10(T(|x|)+1)\bigr)+1
&=22T(|x|)+21\le23(T(|x|)+1).
\end{aligned}
\]

Thus the seam argument gives the public bound `23·E.k·(T |x|+1)` at every time, in both decision and find modes. It does not multiply space by the round count. The old decision-loop space row follows since `T+1 ≤ S+T+1`, so deleting its 14-lemma S-form ledger remains justified.

The six filled public specs keep their round-1 types. Their proof dependencies in part 2 are as follows; none of the three removed gate-shim blocks remains.

| Spec | Actual supporting declarations and resulting behavior |
|---|---|
| `loopHostTM_contracts` | The moved `loopHost_contracts`, dropping only its two head clauses. |
| `loopHostTM_decides` | The preceding public contract and `loop_halted_run`; the output is whether any candidate in `List.range (R+1)` accepts, within `10(T+1)(R+2)`. |
| `loopHostTM_finds` | The same contract and `loop_find_run`; the output is the first accepting candidate's payload, or `[]`, within the same time bound. |
| `loopHostTM_spaceUsed_le_budget` | The moved extended contract and real `seamed_space`, followed by the displayed arithmetic. |
| `emitLoopTM_computes` | The existing emitting-row construction over the named host; its preparation call uses `forward=true` and discards the new conjunct. It emits the concatenation of exactly the `R+1` specified chunks. |
| `callTM_run` | The surviving `emCall_first`; its full first-exit condition includes time zero and its endpoint matches the install/emit mode. |

The following adversarial instantiations test literal boundary behavior. These are mathematical/source substitutions, not claimed Lean executions.

| Instantiation | Check and outcome |
|---|---|
| Zero fuel work tapes | Choose a zero-tape fuel machine that emits nothing and halts in one step, `R=0`, `T=1`. The quantified fuel-head clause is over `Fin 0` and is vacuous, while preparation still has a real positive halting run and a host endpoint. |
| `forward=true` | Use that fuel machine and a zero-tape body whose initial state is its anchor and whose stationary one-step round returns to the anchor while emitting `[true]`. With constant empty orbit state, invariant `True`, `R=0`, `T=1`, the emitting host emits one chunk; fuel preparation still returns the same bounded residue. |
| `T x.length=0` | `hF x` would require the initialized fuel configuration to be halted at time zero, but its state is `some q₀`. This case is explicitly impossible, also covered by `Finite.lean`'s `not_computesInTime_zero`; it is not a missing positivity hypothesis. |
| A fuel head left of the origin | Use one fuel work tape and a one-step machine that moves its head left, emits nothing and halts, with `R=0`, `T=1`. The actual retained head is `-1`, attaining the lower bound; a one-sided or natural-valued replacement would fail, while the supplied integer interval succeeds. |
| `R=0`, rejecting only candidate | Use a zero-tape body with anchor as initial state, a silent stationary one-step return, constant empty orbit state and `acceptF=false`, with the one-step empty-output fuel machine. Candidate zero is processed once; the exhausted output is `[false]` in decision mode and `[]` in find mode. |
| `R=0`, accepting last candidate | Instead let the body's one-step transition halt with payload `[true]` and set `acceptF=true`. The actual run accepts, whereas the separately specified exhausted terminal is a halted copy of candidate one with the exhaustion output. No clause requires the accepting run to reach that terminal; its head bound follows from the canonical candidate. |
| `segment_heads`, `N=0` | Take a halted configuration whose one head is at `H+B`. The run is constant and attains the asserted upper bound; the nonterminal seam and segment hypotheses are vacuous, but the terminal hypotheses are essential and sufficient. |
| Early halt before a designated next seam | Take `N=1`, `H=0`, `B=1`, seam zero at the origin, and a one-step left move followed by halt. A separately supplied halted terminal can be at zero. The segment's halt alternative suffices: every later actual head remains at `-1` and never needs to reach the designated terminal. |
| Zero segment budget | With `B=0`, a segment must already be halted or equal the next seam at time zero. Induction over finite `N` reaches the halted terminal even if several consecutive seams coincide; no unspoken positive-duration condition is needed. |
| `space_radius`, `B=0` | A stationary `k`-tape machine has exactly one visited position per tape, even at time zero, so total space is `k=k(2·0+1)`. The `+1` is necessary. For `k=0`, both sides are zero. |
| Budget arithmetic at `T=0` | The numerical inequality becomes `2(0+10)+1=21≤23`. Although the fuel hypothesis excludes this machine-contract instance, the arithmetic bound itself has no exceptional zero case. |
| Preparation retarget without the repair | The original home lemma still does not expose the fuel-head conjunct. The supplied tip control fails at the preparation example; adding the clause restores exactly the premise consumed by `loopCall_heads`. Definitional equality of the host machines alone would not do so. |

The retarget table's population is complete for its stated purpose: the 47 moving declarations, including the two public rewind lemmas, and 12 absorbed declarations. I reproduced its 215 declaration-to-declaration dependency entries, scanning statements and proofs; these are distinct dependency edges, not counts of repeated textual occurrences. The classes reproduce as **53 IDENTICAL, 112 MOVES-WITH, 11 GENERALIZATION, 1 repaired-WEAKER, 38 NOT-CARRIED**. No private retarget crosses a home boundary.

The 38 NOT-CARRIED entries are accounted for individually by the following replacement routes.

| Discarded declaration(s) | Entries | Why the old region dependencies are unnecessary |
|---|---:|---|
| `f2_counter_computes` | 4 | `lengthBitsTM_computes` uses the original `timeConstructible_id` proof over the home counter lemmas. |
| `f2_unary_sharp` | 3 | The named unary witness uses `constTM_computes` in degree zero and the original `catalogPoly_unary_computes` otherwise. It needs no Catalog space-row witness. |
| `f2_strip_linear` | 6 | The probe derives the named strip spec from the home extract/marker/strip lemmas, composition and `timedCondTM_computes`. |
| `f2_cond_time` | 4 | The named timed-conditional spec uses the original Wrappers row body and its local phase lemmas. |
| `f2_splitSolve_of_body`, `f2_splitSolve_source`, `f2_splitSolve_closed` | 7 each | The named split witnesses, home body/source contracts and `MIG1Probe.split_*` glue derive the time and space specs from the public loop specs and length counter. The three copied split proofs are discarded, including their references to Catalog's existential space rows. |

The Loop-only negative control leaves no identified non-Loop comparison gap: the only four non-verbatim sourced copies outside Loop are those three absorbed split lemmas and the statement-identical `f2_splitBody_round`. The 20 Loop-copy examples and additional interval example regenerate exactly; the repaired file has 21 examples and the tip file 20. The supplied Lean log reports zero errors after part 1 and the two expected failing examples at the tip. For the contract example, the old existential-coefficient shape is also incompatible with the new explicit-coefficient application; the diagnostic should not be read as isolating only its missing head clauses.

The six interval retargets require MIG-0b, and the three sum retargets require F-A's `Mathlib.Algebra.BigOperators.Fin` import, as reflected in R2-3. For the available source subset, I reproduced all table fields except two TimeConstructible accessibility booleans: their import paths pass through unbundled `StateRenaming`/`Robustness` sources. The complete-tree accessibility result for those paths remains log-backed; this is not evidence of an inaccessible retarget. The supplied sources establish all same-home private access and the other relevant direct import paths. The public duplicate uses have the stated interval conversion, sum theorem, pair-decoding inverse, or input-head bound available under the planned imports.

The depth-aware statement comparison confirms the packet's additional claim: of 264 sourced copies, the old cut ended early for `f2_counter_emit`, `f2_loopHost_frame_replay` and `f2_loopHost_round`, and correcting the cut changes **no identity verdict**.

The overlay is an adequate pre-landing check of these Loop edits: it contains the complete modified file, imports precisely Loop's six imports plus `Simulation`, does not import `Loop`, and replaces the shims with the actual declarations being tested. Independently applying its three supplied diffs yields exactly the generated part 1, part 2 and stand-in. The 12-hunk part-1 diff has **+219/−19** lines; no added line exceeds 100 columns. All 63 over-width part-1 lines are inherited. Source comparison reports exactly the two private statement changes, the stand-in and four moved private lemmas, and body-only changes to `exists_loopCfgTM`, `exists_loopFindTM` and `exists_emitLoopTM`. No `f2_`/`a2_` identifier or proof admission remains in the overlay's code.

The raw overlay transcript independently counts **0 errors, 0 sorry warnings, 61 other warnings and 23 axiom reports**, with no axiom outside `propext`, `Classical.choice`, `Quot.sound`. Every warning location maps to an unchanged line of the original Loop source. Exact equality with the baseline warning multiset is reported by the supplied checker, but its full baseline transcript is not included; I therefore do not claim an independent rerun of that comparison. The separate maintainer rerun is an attestation, not a second independently inspectable transcript.

The runner's core round-1 defect is repaired: elaborator status is retained, expected results are compared, failures are accumulated, and the final exit is nonzero on deviations. The supplied one-token control records 14 deviations and exit 1; I independently reproduced the exact three identity failures and the missing-consumer-file control. Independently exercising the builder with a missing directory, empty templates, wrong template count, duplicate `.lean`/`.lean.txt`, missing source, and unknown requested declaration gave exit 2 and preserved the target in all six cases. R2-1 and R2-2 delimit the remaining claims the runner does not enforce.

The bundle repair is substantive: all named manifests, templates, scripts, consumer-name input, overlay, checks and 14 round-2 logs are present. `BUNDLE-MISSING.txt` correctly says that reproducing the complete name/import screens and Lean runs still requires the full checkout, its olean snapshot and MIG-0b's full landing set. Applying the supplied `Finite.diff` to the supplied `Finite.lean` reconstructs the stand-in's source exactly; the missing full MIG-0b set is not needed for that comparison. The evidence map's 36 reused inputs are present, but their claimed equality to separately committed repository files cannot independently be checked without those repository versions.

The three corrected descriptions are right. The reproduced style lint gives **0 FAIL, 2 WARN over 3 files**: the unit and full spec probe cause the size warnings, and the bridge does not. MIG-0b's notes are bundled, and their §3/§10.6 explain the changed layering rationale. Exactly the two retired rows with code consumers, copy and transfer, have the four-line re-derivations; the other four require no code-site replacement.

The following table records the disposition of the remaining attestations, including the post-measurement note.

| Attestation | Audit disposition |
|---|---|
| Ten MIG-1 files unchanged between round 1 and `99ad2f98` | **Source hashes corroborated:** all ten supplied files have exactly the Git blob IDs listed in the provenance log, computed independently as Git blob hashes. Equality of those blobs at the two repository commits is supported by the supplied read-only Git log, not independently queried history. |
| Unit, spec tail, bridge and axiom-print list unchanged | **Independently reproduced.** The rebuilt unit is 2,950 lines, the tail 1,162, the bridge 321, and the full spec probe 4,112. The axiom-print name list is identical; the generated axiom-tail comment differs as explicitly described by the runner. |
| 158 identities and exact three-mutation control | **Independently reproduced:** 97 verbatim, 47 statement, 7 substring, 3 transform and 4 binder checks, zero failures. The mutant exits 3 with exactly `timedCondTM`, `loopHostM`, `prependTM_computes`. These checks retain their documented, differing strengths. |
| Unit/spec/bridge elaboration and eight cuts | **Lean results supported by supplied logs.** The unit reports 31 sorry/6 other warnings, the spec probe 70/6, the bridge 0/0, all with zero errors. I regenerated all eight cut files with the stated line counts and exact eight-import union; I did not elaborate them. |
| 130 public axiom reports, 46 sorry-free, 84 with `sorryAx`, no nonstandard axiom | **Supported by the supplied axiom log and independently checked print-list inventory.** This is the statement unit's result, not a certificate for the later in-place migration. |
| Name screens: 14,300 declarations in 575 modules; one intended moved clash; no other clash/exposure/package hit; MIG-0b 1,211 declarations in 15 files | **Complete-tree results remain log-backed.** The unit's public names and moved-name map reproduce. The absent package sources, full repository and full MIG-0b landing set prevent independently repeating these entire screens. |
| Deletion table: 378 declarations, 9,172 lines, two changed rows, no unassigned fate | **Independently reproduced byte for byte**, both round-1 and round-2 tables. The changes are exactly preparation's strengthened-home disposition and `f2_head_steps`'s duplicate disposition. |
| Consumers: 53 rows, 221 citations/35 files; 34 home rows, 216/33 | **Recomputed from JSON.** All code and declaration entries are identical between the two measurements. A fresh scan of all 15 supplied source modules agrees exactly with the corresponding slices of the full inventory. The other consumer modules are unbundled. |
| Comment mentions 191→194 and the new F-D site | **Independently checked:** the only added entries are `FormulaKit/Emit.lean:19,29` and `RAMSimulation/WordSize.lean:75`. They are comments, not code citations. `WordSize:75` names the retained Catalog row at old line 4318, so F-D must refresh that location or remove the fragile line reference. |
| Replay closures 212/212/212/82/97/34/34 of 632 modules | **Enumerations and deltas checked.** Each logged list has the claimed number of distinct modules and loses none from round 1. The six additions for whole/S/F-A/F-C are FormulaKit, FormulaKit.Emit and the four RAMSimulation modules; F-B adds the two FormulaKit modules, F-D the four RAMSimulation modules. Attribution to PRs #85/#86 and the complete import graph remain supported by provenance/logs rather than a fresh full-tree graph computation. These lists are not compilation replays. |
| R3's 24 checks | **Independently reproduced at the measurement base.** The bundled CodeSimulator site is still line 1295. Later line positions require the later source. |
| Decision 2's eight specs and sorry-free batches | **Text scan reproduced and dependency routes inspected.** `callTM_run`, `redirectTM_runFrom`, `polyUnaryTM_computes`, `pairLenCheckTM_computes` are scheduled sorry-free at S; strip waits for F-A; all three split specs wait for F-C, including their F-A length-counter dependency. This is a staging analysis, not a kernel result for future commits. |
| Decision 3 and revised F-C | **Consistent.** MIG-0b supplies the primitive interval proof; H2's absolute-value name becomes its compatibility corollary. MIG-1 omits its duplicate public head addition, leaving 70 landed names. F-C's strengthened preparation, extended contract, four moved lemmas, five fills and six row swaps match the overlay. |
| Environment: Lean 4.25.0, `oleans-t1`, no olean writes, no network/lake, isolated Python, read-only Git, clean worktree, unchanged index mtime | **Historical execution attestations, not independently established.** The shown runner commands, helper quotation and provenance records are consistent with them. No complete before/after filesystem record, snapshot contents or independently recorded session is supplied. |
| Runner exit 0/`RESULT: PASS`, 133 seconds; maintainer re-elaboration | **Supported as execution attestations.** The reported successful counts are internally consistent with the supplied source artifacts and logs. The duration and separate maintainer rerun are not independently reproduced; R2-1–R2-2 limit the claimed general failure guarantees. |
| Post-measurement H2-M (#88): staying declarations frozen, only relevant CodeSimulator site shifted to 1282 | **Not independently verifiable from this packet.** Updated backlog/design prose records the move, but the post-H2-M CodeSimulator, move diff and freeze results are not supplied. The bundled file is explicitly the old measurement-base blob, so it cannot certify line 1282 or the later freeze. |
| Post-measurement ARM merge `8c23f3bc`: none of the ten files touched, two length-counter citations, 706 modules/282 closure at `dc891632` | **Not independently verifiable from this packet.** The later changed-file list, `TQBFHardVerifier.lean:247,264`, and later graph enumeration/provenance are absent. The updated backlog corroborates the occurrence of the merge only at the level of maintainer records. Do not treat the `99ad2f98` logs as evidence of these later numerical and freeze claims; retain them as maintainer attestations pending S's required re-measurement. |
| Net saving about 7.0k lines | **An estimate, correctly labelled.** Its deletion-inventory inputs reproduce; the actual in-place diff is still needed for a final total. |

No mathematical counterexample or remaining deletion-plan major was found. The statement gate can close under its zero-blocker/zero-major rule. This does not certify the later campaign tip, application of the in-place renames, the future F-C replay (97 modules was the measured old-base closure), or the other fill batches; those obligations remain exactly where the pack places them.

Notation glossary: `r2/` abbreviates `audits/evidence/mig1/gate/r2/`; `|x|` and `|word|` denote list length. `u` is the fuel machine's first halting time, `c` its configuration at that time, and `v` the preparation input-rewind duration in the displayed calculation. `T`, `R`, `B`, `H`, `N`, `M`, `E`, `k`, `cfg`, `t` and `i` retain their local meanings from the audited declarations; `k` denotes the relevant number of work tapes. No other new mathematical notation is introduced.
