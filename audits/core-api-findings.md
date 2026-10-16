The SHA-256 matches `fc8219a63b5c818d5ed4937221cabc18aa10b43b99f77f95b238f93798f078e5`. The bundle contains **63 sections**.

The added equations are faithful, but **U2-S’s API remains incomplete under the literal no-unfolding rule**. I also inspected four omitted dependencies—`CleanSweep`, `Finite`, `Contract/Basic`, and `Build/Seam`—at the [audited commit](https://github.com/Shilun-Allan-Li/tcslib/tree/d5255232d8ff15dcb21cf8caeaf961f69453bf13). I did not independently run Lean; elaboration conclusions below refer to the supplied logs.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `Machines/CleanSweep.lean` · `cleanTM`; U2-S draft | The cleaned canonizer’s initialization still requires reading an unpublished field equation. | `initCfg_eq` exposes `Cfg.init (cleanTM M q).q₀ input`, whereas `cleanTM_run` starts at `Cfg.init (.init q) input`. Neither `CleanSweep` nor `Clean` publishes the intervening initial-state equation. Their run lemmas concern explicitly supplied configurations and therefore do not establish the machine’s default start state. | Publish `(cleanTM M q).q₀ = .init q` beside `cleanTM`, or an equivalent initialization theorem, and add it to U2-S’s probe. Also inventory initial-state equations for the chosen assembly: the returning embedding and phase/seam run lemmas likewise start from explicit configurations. |
| 2 | **major** | `Finite.lean` · `FinTM.ComputesFunInTime`; U2-S draft, step 1 | Constructing and reading the required function-computation predicate still relies on reducing an imported definition. | The draft mandates proving `F'.ComputesFunInTime …`. `computesInTime_iff` exposes only the inner, single-input predicate. The outer `ComputesFunInTime` is a `def`, with no published equivalence or general introduction/elimination pair in its defining module. Introducing its input argument directly uses the definitional reduction forbidden by rule 10. | Publish an equivalence with `∀ input, M.ComputesInTime input (f input) (T input.length)`, or equivalent introduction/elimination lemmas, in `Finite.lean`; update the inventory and probe. |
| 3 | **minor** | `audits/core-api-pack.md` · consumer evidence | The consumer snapshots do not support all the pack’s descriptions. | The supplied `ZoneRebalance.lean` is the **331-line, zero-private** version, not the **570-line version with 18 helpers** described in the delivery review. The supplied `StepBlockForward.lean` is the **132-line skeleton**; its reference to the moved lemma is in the proof sketch, so it does not demonstrate resolution of #114’s actual proof citations. | Include the reviewed consumer versions or clearly label these as baseline snapshots. Check the actual consumers in the merged replay. |
| 4 | **minor** | `logs/axioms.log`; `NOTES.md` | The axiom evidence omits one handwritten addition. | `serializeK_eq` is absent from the log. The other 45 explicit additions/relocations are represented. Its `rfl` proof presents no apparent soundness concern, but the blanket logging claim is inaccurate. | Append its axiom print or narrow the attestation. |
| 5 | **minor** | `Configuration.lean`, `Deterministic.lean` · vendoring headers | The local-modification inventories omit this PR’s mathematical additions. | The headers still say the mathematical content is unchanged, or unchanged except for the listed modifications; those lists omit the new equations and relocated visited-set lemmas. The later module summaries do disclose them. | Update the vendoring inventories, distinguishing preserved upstream definitions from added API lemmas and relocated results. |

Answers to the pack’s seven questions:

1. **Faithfulness and case coverage.** No incorrect equation or omitted case was found among the **45 generated field equations** and **46 explicit additions, including the two relocations**. The generated fields preserve the definitions’ binders, guards, state encodings, and tape placement. Function-valued fields are correctly stated pointwise; omitted proof fields require no computational equations.

   The requested case families are exhaustive: input positions split into the left blank, interior, and right blank; natural-number guards split into `<` and the complementary `≤`; Boolean arguments have both constructors; integer positions have negative/zero/positive cases; and `zoneCellOfCell` covers blank, binary, and zone cells. Together with the existing `zoneStart_eq`, the API determines all **32 value definitions** in `Zone` and `ZoneTape`.

2. **The move.** Both moved statements and proofs are textually identical after normalizing the declaration-name prefix. Their full names remain `Turing.MultiTapeTM.visitedByTapeHead_*`. Apart from their removal, `StepBlock` changes only the two documented passages. Its actual citations retain the same names. Verification of #114’s delivered proof remains limited by finding 3.

3. **Behaviour preservation.** Confirmed from the patch: no existing definition or theorem statement changes, no new admission, and no new `@[simp]`. Every new `simps` invocation specifies `isSimp := false`. I reversed all five patches successfully and verified every before/after Git blob prefix against the reconstructed files.

4. **Route coverage.**
   - **U2-S:** incomplete for findings 1–2. The serialization, buffered configurations, capture placement, and frame equations themselves suffice. The rewind’s exact time can be obtained using the published `rewind_scan` and `controlAction_apply`; its existential bound alone is insufficient.
   - **F5:** no additional gap identified in the audited core interface. Its own `inputCell`, `RulerAt`, and `rulerHostCfg` may be unfolded; the reading, movement, embedding, and visited-set APIs supply the external facts.
   - **G4:** the **zone-data portion** is covered, including extension, scan semantics, guarded stages, mirroring, and mapped-slot operations. Full dispatch readiness still depends on the separately gated #112 contract API and checking the actual continuation inputs.

5. **Placement.** The defining modules are appropriate homes. Moving the visited-set lemmas into `Deterministic` is appropriate. Their restriction to `Bool` and `Type` can be generalized later; preserving it here maintains the move’s exactness.

6. **Duplication.** Both supplied screens reproduce **byte for byte**:

   | Measurement | Base | Head |
   |---|---:|---:|
   | Screened declarations | 462 | 468 |
   | Reported pairs | 103 | 103 |
   | Reproduced characters | 21,874 | 22,142 |

   The renamed pair is the existing visited-set overlap after relocation. The additional 268 characters come from attributes attached by the screen to existing mirrored definitions. **No new copied proof family was found.**

7. **Records.** Findings 3–5 identify the discrepancies. The supplied nine changed-file elaboration comparisons report zero errors and unchanged warning counts. Lint retains the same warning categories and files. The full replay is described as future work; no completed replay log is supplied.

Adversarial checks included:

- **Empty input:** its only positions, `0` and `1`, both read blank.
- **Zero zone levels:** slots are unoccupied; guarded moves and rebalance are identities. Extending creates stored virtual blanks at cells `±2` and unoccupied slots at `±3`, preserving the distinction between physical blank cells and empty slots.
- **Empty patch and interval boundary:** `wordPatch` with an empty word preserves every cell; the upper endpoint is outside the patch.
- **Disabled guards:** out-of-range shifts and moves into a full receiving side retain the identity branches.

**FAIL — 0 blockers, 2 majors, 3 minors, 0 notes.**
