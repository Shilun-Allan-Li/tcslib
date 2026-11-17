# gsw-6a-statements · maintainer delivery review (r1)

**Verdict (interim, phase 1 of 2): ACCEPT WITH ONE LANDING EDIT, pending one ruling and the phase-2 Lean checks.**
- Both series reproduce hash for hash. The 18 changed paths are exactly the brief's scope. decls2 gives 271 ADDED,
  0 CHANGED and 0 REMOVED, equal to the delivered TSV.
- I read every statement against r3 and P6-Q1..Q19 and re-derived each constant marked *(fix)*. No statement is
  false, vacuous or mis-quantified, and no change of meaning against r3 was made.
- Admissions are exactly the 100 targets: the root build gives 229 + 100, recounted from 1,345 raw logs.
- Phase 1 found 0 blockers, 1 major (G6A-F01), 3 minors (F02–F04) and 9 infos.
- **G6A-F01 needs Seyoon's ruling.** `TreeCircuit.rename` with `rename_eval` and `depth_rename` restates the public,
  proved `TreeCircuit.reidx`, `reidx_eval` and `reidx_depth` (`BooleanAnalysis/LMN/CircuitReindex.lean`).
  - Neither the REPORT nor r3 §H2 discloses it.
  - Recommended: the landing edit **LE-ren** (`landing/LE-ren-proposed.diff`), which drops `rename` and its three
    declarations. Admissions go 100 → 98 and `Combinators.lean` 659 → 629 lines.
- The verdict becomes final only after phase 2 (below).

Scope note: bootstrapping and circular security are 6b (Gate 46), not this job. Nothing under `Cryptography/` is
delivered and no `[Gen09]` is cited, so there is nothing of either to review here.

## Delivery and landing
- **Delivery:** Claude, a lead with two sub-agents (`bp`: BranchingPrograms; `fa`: FormulaArith F1–F3, CarrySave,
  Compare, ModSum).
  - Final: exchange `d7a9adb5b70c70c1b6fb8dc3d0aa5a60d720c1ef` ("stmt gsw-6a: final", 2026-11-17 05:09, unsigned).
  - Checkpoint 1: `c0e11b31` (reviewed in `../checkpoint1-6a-review.md`).
  - Both commits touch only `inbox/fills/gsw-6a-statements/`, and no later exchange commit touches that path.
- **Issue base:** `f6f295a6`. Series heads:
  - `owner/o1-balanced`: `413e9aa42f6b96b4d65673c37c83819b2fb77579`, unchanged since checkpoint 1;
  - `stmt/gsw-6a`, on O1: `ad8e170f` (Defs, Eval), `0c39a064` (Barrington, Converse, NC1, facade), `4981a2a9` (NAND
    form, layering), `5159f5c9` (FormulaArith), `ec36703b56513d575036fa75ddb0b2b9d3f893b6` (registrations, §14 rows).
- **Files** (base → head):

  | Path | Change |
  |---|---|
  | `BranchingPrograms.lean` + `BranchingPrograms/{Defs,Eval,Barrington,BarringtonConverse,NC1}.lean` | new: 39 + 412/172/463/304/135 lines |
  | `CircuitComplexity/{NANDForm,NANDLayering}.lean` | new: 284 and 388 lines |
  | `CircuitComplexity/FormulaArith.lean` + `FormulaArith/{Combinators,CarrySave,Compare,ModSum}.lean` | new: 31 + 659/297/238/196 lines |
  | `CircuitComplexity/TreeNCAC.lean` | O1 only: 537 → 359 lines |
  | `CircuitComplexity.lean` | +12 lines (3 imports, contents) |
  | `ComputationalModels.lean` | +21 lines (1 import, 2 models, 4 conversions, [Bar89]) |
  | `TCSlib.lean` | +1 line (Complexity block, line 28) |
  | `machine-library-design.md` | §14 status sentence, rows H18–H20, new subsection "Circuit and formula gadgets" |

  - Placement: all models of computation are under `Complexity/`, as the location ruling and Seyoon's standing
    direction require.
  - Nothing under `Cryptography/` or `blueprint/`. `DAGCircuit`, `DAGTransform`, `DAGFanin`, `TreeDAG`, `Basic`,
    `NCAC`, `Adder` and `Parity` are unchanged.
- **Records tip** at review: `b9860ca888b12fe66be3824733b89e921e24ee05`, Lean-equal to `463f2244` (snapshot #4 T,
  after #351 and #352).
  - Since the base, only `TCSlib.lean` (#331, Cryptography block) and `Uniform.lean` (#341) changed among
    6a-relevant paths. `Uniform` is not in any 6a closure, and the downstream of the changed modules is the same at
    base and tip.
- **Merge checks** (`git merge-tree --write-tree`; all clean, 0 conflicts):
  - tip × O1 → `fd9a242f…`;
  - tip × stmt → `31a37a04…`. The 17 other files are blob-equal to `ec36703b`, and `TCSlib.lean` is the tip's plus
    the one import line;
  - stmt × #340 `916afc25` → `f4e92964…` and stmt × #346 `89a18a82` → `292f1b60…`. Neither PR touches a 6a path.
  - The running cleanup Stage 1 job lists the 6a paths as forbidden and keeps `TCSlib.lean` frozen. Its 21 scope
    files are disjoint from these 18.
- **Evidence:** `gsw-6a-final-r1-phase1-evidence.zip`, SHA-256
  `ef2b38ecfb1bdbcdea8832d7707c4ce070eb9eacf101c8ffed9afaa61531aa90` (22 entries; `evidence-SHA256SUMS` beside
  this file). It holds `PROVENANCE.txt`, `integrity/`, `statements/` (decls2), `citations/`, `clash/`, `lint/`,
  `recount/`, `landing/` (merge checks, downstream, `LE-ren-proposed.diff`) and `tools/` (`citecheck.py`, `names.py`,
  `closure.py`, `recount.py`, unmodified `decls2.py`), with its own `SHA256SUMS`.

## Checks (phase 1)
- **Integrity.**
  - Manifests verify, with exact path sets and no `./`: top level 2137/2137, `evidence/` 2105/2105.
  - The issue package verifies 7/7. Plan r3 `06824b3d…` and rulings `312fef45…` are equal at the records pin and in
    the pack.
- **Reproduction.**
  - `git am` at the base, in a sparse scratch worktree with `COMMITS.tsv`'s committer data and no signing,
    reproduces all six hashes.
  - The signing column is `none` throughout, and the commits are unsigned.
  - `src/` equals the 18 changed paths byte for byte, and `src-o1/` equals O1's four files.
  - From O1 to the head, `Combinators.lean` is a pure insertion (+413/−0), so O1's text is untouched.
- **decls2** (maintainer copy, run in the reproduced worktree, empty `.err`): 271 ADDED, 0 CHANGED, 0 REMOVED, equal
  to the delivered `stmt/decls2.tsv`. All 271 names appear in the delivered `StmtDump`.
  - The ADDED list is r3's definitions, targets and readers, plus disclosed public helpers, each with readers:
    `layerChain`/`layerAt`/`layerColumn`/`layerFold`, `conjugatorIndex`/`Fun`/`Table`, `commutatorProgram`,
    `csaLayer`, `constBits`, `maskedConst`, `Instr.isPermutation_ofPerm`, `language_eq` and four decidability
    instances (G6A-F08).
- **Statements.** I read every declaration of the 13 new modules against r3 §H5.1–H5.8 and the rulings:
  - **Branching programs** (P6-Q4).
    - The model is general (maps `Fin w → Fin w`) with `IsPermutation`, BV14's field order, and `yield` in program
      order (`yield_append : (B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x`).
    - `complementLast` post-composes with `σ⁻¹`. Families recognize by accepting sets, and `InBWBP`/`InPBP` bound
      the length by `a·(n+1)^k`.
    - The host `evalWith` is the push form with `Finset` sums. C8 (one-hot to one-hot for general maps) and C7
      (step-indexed relation) are true as stated.
  - **Barrington, Thm 1** (P6-Q2, Q13).
    - `barrington` is computable and total. I traced the AND step: `θ` conjugates the program-order commutator to
      `σ`, so the four blocks yield `σ` on `A₁ ∩ A₂` and `id` elsewhere.
    - I traced the OR step: `N c μ := (barrington c μ⁻¹).complementLast μ⁻¹` recognizes `¬c` with output `μ`, and
      a final `complementLast σ⁻¹` gives output `σ`.
    - C13/C16 assume `maxFanin ≤ 2` and a five-cycle. C14's length bound `4^depth` holds structurally for every
      `σ`, including constant nodes (length 1, depth 1).
    - `FiveCycleRecognizes` includes `IsFiveCycle σ`. C10 assumes five-cycles, and the conjugator falls back to
      `1` off its domain.
  - **Thm 2** (P6-Q3, Q18). I re-derived C19's `(⌈log₂ w⌉+2)·⌈log₂ l⌉+1` (leaves ≤ 1; a split adds
    `⌈log₂ w⌉+2`; `⌈log₂⌈l/2⌉⌉ = ⌈log₂ l⌉−1`) and C21's `topDepth w = w⌈log₂ w⌉+⌈log₂ w⌉+3`
    (`|F| ≤ w^w`). The `w = 0` and empty-`F` cases also hold.
  - **NC1.**
    - C22 needs `IsFaninTwo`, which includes `IsWellFormed`, which is exactly what `toTree_eval`/`toTree_depth_le`
      need.
    - C23–C25 route through `InNC.inTreeNC_one`/`InTreeNC.inNC`. The depth `b·(log₂ n + 1)` and the size
      `≤ 2^(depth+1)` give polynomial bounds, and `n = 0` is handled by the accepting set.
  - **NAND form** (P6-Q9, Q16).
    - I checked `nandGadget` row by row against `GadgetSpec` (`DAGTransform.lean:55`): value, cost
      `≤ fan-in + 2`, `≤ 2` added levels and NAND output gates. N2 is true.
    - N5's `2·depth` and N6's `n + 4·#gates` follow from `RewriteInv`. The not-`IsWellFormed` disclosure is
      present.
  - **Layering** (P6-Q14 B). I traced `layerColumn`:
    - the base reads `a@(δ−1)` and the twin reads `a@δ`. An input's twin is `NAND(¬xᵢ)`, and a fan-in-0 gate's twin
      is `NAND(NAND(x₀,¬x₀))` (hence `[NeZero n]`);
    - each chain link adds two gates, one per level. Every lookup lands in an existing column.
    - So N7 (under `IsNANDForm`), N8 (no hypothesis), N10 (exact depth, since `DAGCircuit.depth = depthAt output`),
      N11 (≤ `2(D−δ)+1` gates per column) and N12–N13 (with `n ≥ 1`) are true.
  - **Formula arithmetic** (P6-Q5).
    - `csaStep` is the full-adder identity bitwise. `carryOut` is generate/propagate.
    - `geConst`: with `p = max|U| |W|+1`, the carry word's top bit is `maj3` of padding and so is `false`, which
      makes F8 hold for every `c`.
    - F9: `S < max M 1 · q ≤ 2^w` justifies the trimming; `j = S / q` is the unique witness when `hi ≤ q`; and the
      `q = 0`, `M = 0` cases agree.
    - F10: `modSumDepth` adds up as stated, and `modSumDepth_le` is r3's closed form verbatim. There is no term
      linear in `log q`.
- **Admissions.**
  - Source level: exactly 100 `sorry` (Defs 11, Eval 5, Barrington 11, Converse 11, NC1 5, NANDForm 6,
    NANDLayering 7, Combinators 26, CarrySave 7, Compare 7, ModSum 4).
  - Every `sorry` is in a `theorem` whose docstring has a row marker, a tag or "Glue", its deviations and a
    `**Proof sketch.**`. No definition contains `sorry`.
  - Root build: 329 = 229 (`base-sorries.txt`, 52/52 modules exact) + 100, with 0 mismatches.
- **Docstrings, sources and citations.**
  - Every new public declaration has a formula docstring, and every target a sketch.
  - All 112 anchors exist in their tag's ingest (`citecheck.py`). 18 quotations match textually. The other 6
    differ only in rendering (LaTeX against Unicode) and were each read against the ingest
    (`citations/manual-quotes.txt`), as was BV14's Eq. (4) in C6.
  - The quoted "yielded by a each instruction" is the paper's typo, transcribed as printed (sic).
  - No fabricated locator. The reference lines match the ingest headers. No `[Gen09]`; `[AB09]` appears only where
    an existing tag is kept.
- **Style.**
  - Widths are ≤ 100 in every new file. The only lines over 100 are pre-existing ones in `TreeNCAC`,
    `CircuitComplexity` and `ComputationalModels`.
  - No `@[simp]`, global attribute, `native_decide` or micro sign (the matches are in prose).
  - `style_lint`: 0 findings in the new files. The 11 findings in `TCSlib.lean`/`ComputationalModels.lean` are
    identical at the base (my run).
  - `campaign_style_lint --check8b`: the FAIL/WARN line sets are equal at base and final (25/390; 500 → 513 files).
  - Sizes: every file is under 1,000 lines, and only `Combinators` (659) is above the 600-line target (G6A-F06).
- **Clashes and shadowing** (my namespace-resolving scan, `clash/`).
  - The 285 new names (18 private) have 0 clashes with the 30,261 names at the base and the 31,175 at the tip.
  - 11 names are O1's moved privates. There is no `NAnd` and no `toLayered`.
  - Mathlib has no `BranchingProgram`, `InBWBP`, `InPBP`, `FiveCycleRecognizes`, `IsFiveCycle` or `litInput`.
- **Duplication and reuse.**
  - The REPORT's 15 `path:line` rows hold at the base, and `bitsVal`/`prefixVal`/`carryBit` are reused as
    semantics.
  - Undisclosed: `reidx` (G6A-F01) and the special cases `widenCircuit`/`restrictCircuit` (`Hierarchy.lean:110/139`,
    relatives of `rename`/`subst`).
  - Mathlib's `Equiv.Perm.isConj_iff_cycleType_eq` is the noncomputable existence behind C10. It is not restated,
    since P6-Q13 rules a computable conjugator.
- **Registrations.**
  - `ComputationalModels` lists both models and the four conversions in the file's order.
  - Every line reference in H18 (`Eval.lean:65/73/83/89/99/108/124/143/167`), H19 (`DAGCircuit.lean:149/625`) and
    H20 (`DAGTransform.lean:68/246/263/269/273/278/286`) points at the named declaration.
- **Delivered evidence, recounted from the raw logs** (`recount/recount.out`; regex `^\S+\.lean:\d+:\d+: error[:(]`):
  - **Sweep.** 1,353/1,353 rows, equal to `order-final.txt` (prefix 8, bootstrap 1,325, closure 19, root 1). All
    have rc 0 and 0 errors, and every one of the 1,345 logs recounts equal.
    - The 19 closure modules and the root are hash-bound to my reproduced head (root `d379285a…`).
    - The 1,325 bootstrap sources equal the base and the final.
  - **Seals** (16 files × A/B/coe-A/coe-B): `requested = verified` with 0 errors, except two cases.
    - `TreeNCAC` fails twice, pre-existing (G6A-F05).
    - The `CircuitComplexity` facade overflows the stack unchunked. Chunked into 4 commands it passes, and the
      chunks sum to 3,727 requests.
    - Root, chunked into 14 commands: 13,762/13,763/13,761/13,762 requests, 0 errors.
  - **Controls:** 30/30 OK (10 owners × three runs).
  - **Axioms:** 548 constants, no non-standard axiom. `sorryAx` appears in exactly 105: the 100 targets, plus
    `toNANDForm`/`toNANDForm_eq` through N2 only and `layerNAND`/`_gates`/`_output` through N12–N13 only. Each
    target's trace reaches only itself.
  - **Probes:** 26 rc 0. `T0_Env`'s 4 errors are expected, and P10b5's dropped row is disclosed.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| G6A-F01 | **major, undisclosed duplicate** | `TreeCircuit.rename c e` (`Combinators.lean:368`) is extensionally `TreeCircuit.reidx c e` (`BooleanAnalysis/LMN/CircuitReindex.lean:24`, public since 2026-10-05): both send `⟨i, s⟩` to `⟨e i, s⟩` and keep gates. The targets `rename_eval` (`(c.rename e).eval x = c.eval (x ∘ e)`) and `depth_rename` (`= c.depth`) restate the **proved** `reidx_eval` and `reidx_depth`. Neither the REPORT's overlap table nor r3 §H2 lists `reidx`, so this is a plan-level miss that the delivery inherited. The policy grades it a major. No 6a or 6b consumer of `rename` exists (r3 has no use outside F2). | **Ruling needed (Q1).** Recommended: **LE-ren** (`landing/LE-ren-proposed.diff`, −38 lines) drops `rename`, `rename_eq`, `rename_eval` and `depth_rename`, and points the docstring, the facade contents and the gadget row to `reidx`. Admissions go 100 → 98 and F2 keeps `subst`'s three lemmas. Add a dedup-queue entry to move `reidx` and its two lemmas into `Combinators` (owner-side, with `widenCircuit` re-pointed). REPORT erratum: add `reidx`, `widenCircuit` and `restrictCircuit` to § *Overlap and reuse*. |
| G6A-F02 | minor, disclosed deviation | O1 makes five Rule 10 repairs, not the brief's three: also `sumSize_pairUp`/`maxFaninL_pairUp` nil cases, through `sumSize_nil`/`maxFaninL_nil` (`G6A-C1-F02`, REPORT Q1). Without them the new owner fails its seal. They are semantics-free. | Seyoon to ratify (Q2). Recommended: accept. |
| G6A-F03 | minor, fill prerequisite | The reader census names nine MISSING readers in frozen files beyond the expected `gadgetCorrect_iff`. I confirmed each absent at the tip: `Lit.eval_eq`; `TreeCircuit.depth_lit`/`maxFanin_lit`/`size_lit`; `carryBit` case readers; `DAGCircuit.isWellFormed_iff`; `Language.inTreeNC_iff`; the `TreeCircuitFamily` `HasFaninTwo`/`IsPolySize`/`HasPolylogDepth` readers; and `gatesAcyclic_iff`. The sketches of F1–F3, F7, C13, C17, C22–C24 and N12 cite them, so fills U1–U11 cannot follow their sketches under Rule 10 without them. | Ruling (Q3). Recommended: one owner-side reader PR (all `rfl`/`Iff.rfl`, about 15 lines in `Basic`, `Adder`, `DAGCircuit`, `DAGTransform`, `TreeNCAC`), landed before the 6a fills are issued. |
| G6A-F04 | minor, disclosed statement form | N12 is stated in the `args_lt` field's form, not r3's `GatesAcyclic (n + n) C.layerGates`, because `GatesAcyclic` has no reader. The bodies are identical (`DAGCircuit.lean:395` against `:465`), so the meaning is the same (REPORT Q2). | Q4. Recommended: keep the field form; `gatesAcyclic_iff` in F03's PR serves the fill. |
| G6A-F05 | info, pre-existing | `TreeNCAC` still fails its seal twice, at the byte-identical private `maxDepth_map_le`/`maxFaninL_map_le`. It also has 4 pre-existing explicit foreign unfolds (`:188`, `:228`, `:250`, `:268`). | Clean-up part 2, beside the recorded line-366 read. |
| G6A-F06 | info, size watch | `Combinators.lean` is 659 lines (629 with LE-ren), above the 600 target with 26 (24) targets. r3's U8 estimate of 150–220 fill lines projects about 800–880 filled. | Brief U8: split the gadgets into `FormulaArith/Gadgets.lean` if the fill passes 800. |
| G6A-F07 | info, docstring nits | `Combinators`' module docstring still says "promoted unchanged" (five repairs). `depth_subst_le`/`maxFanin_subst_le` call the file's import closure "(frozen)"; it is O1's header, kept byte-identical by choice. The [Bar89] reference line reads "D. A. Barrington … J. Comput. Syst. Sci." in `NANDLayering`/`ComputationalModels`, against "D. A. Mix Barrington … J. Comput. System Sci." elsewhere; the latter matches the ingest. | Docstring-only, optional at landing or in the fill. |
| G6A-F08 | info, disclosed changes | REPORT §6 lists 16 changes, none of meaning: `List.formPerm` for `c[…]` (Q4 there); `Finset.univ.sup` for `⨆`; `carryOut`'s explicit `b`; implicit binders; explicit formulas where r3 named only lemmas; added fan-in lemmas and public helpers with readers; the conjugator table. The settled constants are C21 `+3`, F6 `2⌈log₂ k⌉`, F7 `2⌈log₂ b⌉+3` and F8 `+7`, with F10's closed form kept. I re-derived C19, C21, F5–F10 and N11. | None. |
| G6A-F09 | info | F9's `lo ≤ hi` is unnecessary: my derivation agrees with P10. It is kept as r3 states it. | Keep (Q5 in the REPORT). Dropping it later is a statement change for a ruling. |
| G6A-F10 | info, environment | PFR's 31 modules were compiled with plain `lean -o` into the worker's own olean tree, as snapshot #4's layout has them. The seal tools gained `SEAL_CHUNK` and a `Root` label; the chunk sums equal the unchunked request counts. Two container restarts are disclosed, with interrupted logs kept. | Record in the tooling follow-ups (chunking for facades over about 1,000 requests). |
| G6A-F11 | info | C16's deviation note says "BV14 reads coordinate 1". BV14 §3.3 (p013-b002) outputs 1 iff `ζ_L = 1`, the start state, which is the complement of the five-cycle reading. The note is r3 §H3.7's and harmless; the statement is correct. | 6b's G-series must use the `σ 0` reading, as r3 does. Note for Gate 45. |
| G6A-F12 | info, freshness | The tip is Lean-equal to `463f2244`. The merges with the tip, #340 and #346 are clean, and nothing overlaps the cleanup Stage 1 job. Disk on this host was 3.2 GB free after I removed my own scratch worktree. | Phase 2 needs about 0.3 GB for rebuilt oleans. Check free space at P2-0. |
| G6A-F13 | info, process | The checkpoint-1 finding `G6A-C1-F01` (no `src/` at the checkpoint) is closed by the final. `G6A-C1-F04` (an unnamed head) is closed: the checkpoint's closure source hashes equal the final's for 18 of 19 modules, and only `Defs` changed (the reader `language_eq`, added for lint check 8, REPORT §3). | None. |

## Landing plan
O1 and the statement PR are two PRs, stacked, as the brief prescribes. Each is cherry-picked onto the records tip,
keeping authorship; the committer is Claude, and each commit is SSH-signed with the Co-Authored-By and
Claude-Session trailers.
- **PR O1** (Gate 45, audited as a proof). Branch `land/gsw-6a-o1`, cherry-picking `413e9aa4` onto the tip.
  - Expected tree: `fd9a242f…`, equal to merge-tree tip × `413e9aa4`.
  - No landing edit, unless Seyoon chooses option B of Q2.
  - Its diff is O1's four files.
- **Statement PR**, stacked on PR O1. Branch `land/gsw-6a-stmt`, cherry-picking `ad8e170f..ec36703b` (5 commits).
  - Expected tree: `31a37a04…`, equal to merge-tree tip × `ec36703b`.
  - Then **LE-ren**, as one signed commit, if Q1 is ruled A.
  - Its diff against PR O1 is the 17 statement-series files.
  - Draft against `cryptography/pass-shelat-ch2-4`. Gate 45 (Codex) audits both.
- **Order:** O1 first. Then the statement PR, retargeted to the records branch. The F03 reader PR is independent of
  both and lands before the 6a fills are issued.
- **Merge conditions:** Q1 ruled (and LE-ren built if A), Q2 ruled, the phase-2 checklist passed, and Gate 45
  closed.

## Phase-2 checklist (merged-tree replays on snapshot #4, per `snapshots.md`; one Lean process for this job)
- **P2-0 Tip and snapshot.**
  - Re-fetch the tip. If any Lean or lake file changed since `463f2244`, redo the merge-trees above.
  - `snapmap.py verify $SP/olean-snapshot $SP/olean-snapshot.map-463f2244.tsv` must give 0/0/0, before and after.
  - Check free disk: at least 1 GB.
- **P2-1 Landing branches.**
  - Build both branches as above. `git range-diff` must be 1/1 and 5/5 identical, and the trees must equal
    `fd9a242f`/`31a37a04`.
  - Apply LE-ren only on the ruling (then expect admissions −2 and `Combinators` at 629 lines). Export each and
    compare with `src-o1/` and `src/`.
- **P2-2 Replay R1 (O1 on the tip).** `cp -al` of the snapshot to `$SP/olean-replay-gsw6a-o1`, the overlay,
  `stateplan`/`downorder`/`fullorder`, then `runner.py`.
  - Rebuild the **9** modules `Combinators`, `FormulaArith`, `TreeNCAC`, `NCAC`, `Parity`, `Hierarchy`,
    `CircuitComplexity`, `ComputationalModels` and `TCSlib`.
  - The state check covers the snapshot closure + 2. Every module needs rc 0, 0 `error:`/`error(` and link count 1.
  - Admissions +0. O1's 141 constants must use standard axioms.
  - Seals: `Combinators` 174 and `FormulaArith` 194, 0 errors in all four variants; `TreeNCAC` 2 pre-existing.
    Controls on `balanced` as at checkpoint 1.
- **P2-3 Replay R2 (statements on R1's output).** `cp -al` of R1's output to `$SP/olean-replay-gsw6a-stmt`.
  - Rebuild **20** modules: the 11 new ones (five `BranchingPrograms` files and their facade, `NANDForm`,
    `NANDLayering`, `CarrySave`, `Compare`, `ModSum`); the changed `Combinators`, `FormulaArith`,
    `CircuitComplexity`, `ComputationalModels` and `TCSlib`; and the downstream `TreeNCAC`, `NCAC`, `Parity` and
    `Hierarchy`. A single combined replay of the final tree on the tip rebuilds the same 20 modules
    (`landing/downstream-merged-final.txt` lists their downstream part).
  - The state check covers the snapshot closure + 13.
  - Admissions: the tip + 100 (or + 98 with LE-ren), exactly the targets per module. Other warnings are unchanged.
- **P2-4 Axioms on R2.** The census of 548 constants must reproduce (fewer with LE-ren), with `sorryAx` only in the
  targets and the five N2/N12–N13 dependents, and each target's trace only itself.
- **P2-5 Rule 10 on R2.**
  - Seals: the 16 files in four variants (the facade chunked, `SEAL_CHUNK=1000`), with the request counts above and
    0 errors except `TreeNCAC`'s two.
  - Run coe-A only for the root (the canonical variant; about 45 min).
  - Controls 30/30, and 0 foreign unfolds in the 13 new files.
- **P2-6 Lint.** At the tip and at each head: no new FAIL/WARN line, and `style_lint` 0 in the new files.
- **P2-7 (recommended) Cross-build** of tip × #346 × the statement head, with 0 shared modules expected. Skip it if
  #346 has merged first.
- **P2-8 Order, adopt and record.**
  - Merge O1, then the statement PR. On each merge the prospective-tree diff must be empty, and the replay output
    is then adopted, with a new `snapshots.md` row. Otherwise discard it and replay again.
  - Then zip the phase-2 evidence, finalize this review and add the decision-log row.
  - Delete any replay output that is not adopted.

## Questions for Seyoon
- **Q1 (G6A-F01): the `rename` duplicate of `TreeCircuit.reidx`.**
  - **A (rec.)** LE-ren: drop `rename`, `rename_eq`, `rename_eval` and `depth_rename`, and use the existing
    `reidx`. Admissions 100 → 98. Add a dedup entry to move `reidx` into `Combinators` later. No consumer is
    affected.
  - **B** Keep the name: redefine `rename c e := c.reidx e` (importing `LMN/CircuitReindex`), and prove
    `rename_eval`/`depth_rename` now from `reidx_eval`/`reidx_depth`. This makes the core formula layer import a
    `BooleanAnalysis/LMN` file.
  - **C** Land as delivered with a ledger row (disclosed duplicate) and payback: re-point `reidx` to `rename` in the
    clean-up.
- **Q2 (G6A-F02): the two extra O1 repairs.**
  - **A (rec.)** Accept the five-repair form.
  - **B** Restore the brief's three-repair form, with a seal exception for the two nil cases.
- **Q3 (G6A-F03): the owner-side readers the fills need.**
  - **A (rec.)** One small owner-side reader PR with all nine readers plus `gadgetCorrect_iff`, landed before the
    6a fills are issued.
  - **B** Pre-approve each fill to add its own readers as a scope request (as derand did).
  - **C** Fills prove around the gap by definitional unfolding, with Rule 10 exceptions. Not recommended.
- **Q4 (G6A-F04): N12's form.**
  - **A (rec.)** Keep the field form, which has the same meaning.
  - **B** Restate N12 as `GatesAcyclic (n + n) C.layerGates` once `gatesAcyclic_iff` lands, and fill the field
    through the reader.

**Not yet clear to merge.** Q1 (LE-ren recommended) and Q2 need rulings, and phase 2 (the Lean replays) is pending.
No PR is opened yet.
