# Dedup payback PR: landing notes for the maintainer

**The landing tree is ready for the PR: every check passes (`logs/verify.log`, 60 of 60).** No PR
was opened, nothing was committed or pushed.

Every in-scope item landed, including the user's decisions of 2026-10-14 (backlog ARM-1): D4
extended, G-pairidx added, G-rep deferred and G-vword accepted (§3).

## 0. Base, tools, reproduction

- **Base: the merged tip `ff4cab18`**, taken with `git rev-parse origin/complexity/arora-barak-ch3-4`
  at the start of the run and recorded in `work/base-commit.txt`. It is `c9cc485b` (#95–#97
  merged) plus records-only commits, and its Lean files equal `c9cc485b`'s (asserted). The export
  is read-only, in `work/base/`.
  - The tip moved several times during this work: #94, docs-only commits, #95–#97 (Lean merges:
    `RecordTable`, `Embed`, `NDHost`, `Inclusions`, `CodeSimulator`), then records-only commits.
  - None of these touched a payback file. The precheck asserts this against the live tip.
  - Earlier full runs (at `c52663f1` against `oleans-lh1`, before the user's decisions; and at
    two docs-only tips) were superseded by this one.
- **Snapshot.** `<S>/oleans-ltip3`, the catch-up replay of the merged tip. Its log
  `<S>/fills/replay/replay-ltip3.log` ends `# modules=152 failed=0`; I waited for that line before
  the final run. **Packages:** `<S>/wt-mig1s`, packages only.
- **Tools.**
  - Lean ran only as `bash <S>/tools/leanelab.sh <S>/wt-mig1s <S>/oleans-ltip3 <file>`, with no
    olean written.
  - Python ran only as `python3 -I -B`.
  - Git was read-only: `rev-parse`, `archive`, `cat-file`, `ls-tree`, `diff`, `merge-base`, `show`,
    `status`.
  - No lake, no elan, no sub-agents. Nothing was written outside `<L>`.
- **Reproduce.** Run `bash <L>/scripts/run.sh <S> <S>/oleans-ltip3 <S>/wt-mig1s`. An optional fourth
  argument pins another base revision. The script re-exports the base if the export is at
  another commit, fails closed (the precheck exits 2 before anything is written) and exits 1 on
  any FAIL. The elaborations take about 20 minutes.

## 1. Files

| Path | Content |
|---|---|
| `tree/TCSlib/...` | The 27 landed files (§2): 23 with code changes, 4 with comments only (code identity asserted) |
| `patches/<key>.patch` | `diff -u` against the base for each file (`a/` `b/`, `patch -p1`); each replays byte for byte (`logs/land-edits.txt`) |
| `replay-order.txt` | The replay list, 119 modules (§6) |
| `ledger-map.md` | Every P1, P1+ and manual ledger row, and L049, mapped to its edit with `file:line` before and after |
| `scripts/` | The pipeline. `run.sh` drives `precheck.py`, `land.py` + `edits.py`, `cuts.py`, `probes.py`, `elab.sh`, `freeze.py`, `freezectl.py`, `names.py`, `graph.py`, `hygiene.py`, `lint.sh`, `ledger.py`, `verify.py` and `sums.sh` |
| `logs/` | `land-edits.txt`, `cuts.log`, `probes.log`, `elaboration.log`, `freeze.log`, `controls.log`, `names.log`, `graph.log`, `hygiene.log`, `ledger.log` and `verify.log` |
| `work/` | The export, the cut files (`cut/`), the probes (`probes/`), the raw Lean outputs (`out/`), `api-delta.json`, the lint copies and the negative control. None of it is landing material |
| `SHA256SUMS` | Checksums of `tree/`, `patches/`, `scripts/`, `logs/`, `replay-order.txt`, `ledger-map.md` and this file |

## 2. What lands

- **D1** (`Turing.Cfg.InWindow`):
  - Deleted: ConfigGraph's private `InWindow` and its bridge `inWindow_iff_cfgInWindow`, and
    Codec's public `InWin`.
  - `InWin` had 48 code occurrences in `Codec/{Word,Valid,Step,Langs,Checks,Bridge}` and
    `ExpBFS/Radius`. Its definition and the 3 uses inside the deleted copies go. The other 44,
    and ConfigGraph's 5 uses of its private `InWindow`, are rewritten token for token:
    `InWin N r c` becomes `Cfg.InWindow r c`, the same argument order. The freeze checks that every
    changed statement is exactly this rewrite.
  - Proofs that took the old `∀ i, head ∧ cells` apart now use the two clauses of `Cfg.InWindow`.
    The changed proofs are in Word, Valid, Step, Checks, Radius and ConfigGraph.
  - The initial window cites `Turing.Cfg.inWindow_init`, in Checks, Bridge and Radius.
- **D1's leftover bridge content.** `coreCode_inj` still takes the old hypothesis shape. That
  conversion existed twice: in the deleted bridge, and as TQBF.lean's private
  `codec_core_window`.
  - It now exists once, as the public `Turing.Cfg.InWindow.core_bounds` (ConfigGraph).
  - ConfigGraph's `count_windowed_vertices` and TQBF's `codecRowOf_eq_iff` cite it, and
    `codec_core_window` is deleted.
  - **This deletion is not in the ledger.** Without it the PR would add a third copy.
- **D2, D2h, D5.** ConfigGraph's originals are made public in place: `take_succ_action`,
  `abs_lt_card_visitedWith`, `mem_visitedWith_of_ne_none`, `visitedWith_take_subset`, and
  `runWith_take_inWindow` and `inWindow_of_coreSum_eq` (both restated with `Cfg.InWindow`).
  - Deleted: Bridge's four private copies and `inWin_runWith_take`, and Radius'
    `inWin_of_coreSum_eq`. Their uses are re-pointed. The latter's vertex equation runs the other
    way, so uses pass `h.symm` or `h` as needed.
- **D3.** Bridge's `mem_of_acceptsWithin` was the "accepting branch of any length" step, inline in
  the backward branch of `DecidesInSpace.mem_iff_acceptsWithin_configBound`.
  - That step is now the public `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin` in
    ConfigGraph, with Bridge's proof. The packaged lemma's backward branch cites it; its statement
    is unchanged and its sketch is updated.
  - Bridge's copy is deleted.
- **The s1b block.** Re-measured at the tip: the 11 private declarations `s1b_*`.
  - The six in `Turing.FinNDTM` are at lines 619–700.
  - The five in `Complexity` are at 710–809, inside the `namespace Complexity` block at 706–811.
    The block is now empty and goes too.
  - The name screen finds no consumer. The module docstring's s1b sentence is removed.
  - ConfigGraph goes from 811 to 646 lines. Its imports are unchanged; `Constructible` may now be
    unused (§5).
- **D4, as extended by the user on 2026-10-14** (visibility only):
  - `DAGCircuitSat`'s `eval_tseitinGates_values` and `values_getD_eq_of_eval_tseitinGates` are made
    public. These two visibility changes are the only edits in `CircuitComplexity/*`; the freeze,
    verify and control C6 enforce that.
  - `TQBFHardTseitin`'s copy `values_getD_eq_of_eval_tseitinGates` is deleted (L024).
    `toCNF_extension_iff`'s (⇒) direction cites `DAGCircuit.values_getD_eq_of_eval_tseitinGates`,
    and its (⇐) direction cites `eval_tseitinGates_values` (L025). The module's duplication
    disclosure is replaced by the two citations.
- **D6.** Deleted: TQBF.lean's `b4m*` appendix. At the tip it runs from line 2474 to 3185, 712
  lines plus the following blank line, and holds 45 private declarations, all named `b4m*`
  (asserted).
  - The name screen finds no consumer.
  - `TQBFARM/Semantics`' public twins stay.
  - No deleted declaration was sorried.
- **D7 and `decChain`** (in our `Logspace/InputAccess`):
  - **The chain lemma:** the public `arm_chain`, one induction over increments
    (`up = true`) or decrements (`up = false`) of one register. `arm_increments`, Codec's
    `incChain` and Codec's `decChain` are its instances.
  - **The stride decoder:** the public `boundedDecodeStride_loop`, the induction formerly in
    Engine's `decodeStride_loop`, with the down-step through `arm_chain`.
    `boundedDecode_loop` is its stride-1 instance, and Engine's `decodeStride_loop` cites it.
  - Every public statement of Hydroxyi's is unchanged; only proofs, sketches and the module
    docstring's disclosure paragraph change.
- **L049** (R2-1). `access_width_half` is made public. `halvCount_loop` cites it as
  `access_width_half n (Nat.pos_iff_ne_zero.mp hpos)`.
- **`length_lbStep`.** The shared helper is the public `Complexity.length_pairEncode_drop_le`
  (`ClassNP/PolyTimeBlockLoop`, imported by `TQBFHardParams`, so no cycle).
  `length_xorPairStep_le` is its `1 1` instance and `length_lbStep` its `0 1` instance; both stay
  private.
- **P1+, done (10 of 13 copy-side declarations, plus M2; the other 3 have the user's dispositions,
  §3):**
  - **G-oracle** (4 declarations): the public `Complexity.indicator_inputBitLang` and
    `indicator_inputLenLang` in InputAccess. `TQBFARM/Machine` and `Codec/Run` cite them in
    `orc_bit` and `orc_len` (statements kept), and so do QueryReshape's `drop_bit` and `drop_len`.
  - **G-canon** (2): QueryReshape's private `drop_canon` moves down to InputAccess as the public
    `Complexity.LogProg.drop_canon`. Codec/Parse does not import QueryReshape, so the move avoids
    a new import. Parse's `canon_of_getLastD` and `getLastD_of_canon` are its two directions.
  - **G-outsum** (1): `outSummary_eq_empty_iff` moves beside `outSummary_eq_accept_iff` (ConfigGraph,
    `Turing.`), and Checks' copy is deleted.
  - **G-prefix** (1): `prefixTruth_congr_agree` moves verbatim to `Formulas/QBF`
    (`Complexity.QBF.`). `QBF.prefixTruth_congr` becomes its corollary, and the Semantics copy is
    deleted.
  - **G-tseitin** (1): with D4, above.
  - **G-pairidx** (1, user 2026-10-14): the new public `Complexity.pairEncode_getD_snd` in
    InputAccess, beside `pairEncode_getD`, with a docstring and a proof sketch. Parse's
    `pe_getD_snd` cites it (statement kept). The originals re-point to it too: `Mult`'s private
    `mult_addresses` (L050) and QueryReshape's private `comp_suffix_address` (L052).
  - **M2:** `VWord.getD_drop` cites `List.getD_drop`. That needs a new import of
    `TCSlib.Programs.Util.List` in VWord. The name screen finds no clash with VWord's 52-module
    downstream closure and no `open List` there.
- **Leftovers:**
  - the `SpaceComplexity` facade's two Contents lines over 100 columns, re-wrapped;
  - proof sketches for `numVars_le_length_serialize`, `reflTransGen_stepRel` and `nz_run`;
  - `TQBFHardVerifier`'s Main results entry for `predB_iff` removed, with the prose naming its
    home, `TQBFHardBridge`.
- **R2-5's homes.** No re-point needed an import that would create a cycle. G-canon's move down is
  recorded above; it avoids a new import, not a cycle.
- **Width.** Six added lines over 100 columns are re-wrapped, whitespace only (`edits.WRAPS`).
  Three of them are D1 lengthening an existing line by four letters; the other three are new
  docstring lines.

## 3. Dispositions (user, 2026-10-14; backlog ARM-1)

No item is stopped. The four items that stopped in the first pass were decided as follows:
- **D4 extended (L024):** done (§2).
- **G-pairidx (L050, L052):** done, with `Complexity.pairEncode_getD_snd` (§2).
- **G-rep, `pt_rep_mul` (L033):** deferred to ARM-2 and the user's dedup window. It stays
  unchanged, and `ledger-map.md` records the disposition.
- **G-vword, `vword_whole₂` and `vword_whole₃` (L119, L120):** accepted as not real duplication.
  They stay unchanged, and `ledger-map.md` records the disposition.

Also accepted:
- the extra deletion of TQBF's private `codec_core_window` through `Cfg.InWindow.core_bounds`;
- `arm_chain`'s `bif up` parameterization;
- `drop_canon` keeping its name;
- the follow-up for Radius' window lemmas (§7): they are not moved in this PR.

## 4. Public API delta (`work/api-delta.json`, `logs/freeze.log`)

**(a) D1 restatements of existing public declarations: 28.** Each is exactly the token rewrite.

| File | Theorems | Definitions |
|---|---|---|
| Word | 3 | 1 (`decodeCfg`) |
| Valid | 3 | — |
| Step | 4 | — |
| Langs | 3 | 3 (`validLang`, `acceptLang`, `stepLang`) |
| Checks | 3 | — |
| Radius | 7 | 1 (`WinRun`) |

ConfigGraph's two promoted D1 lemmas are counted under (b).

**(b) Additions: 20 public names.**
- Made public in place (9):
  - ConfigGraph (6): `Turing.NDTM.take_succ_action`, `abs_lt_card_visitedWith`,
    `mem_visitedWith_of_ne_none`, `visitedWith_take_subset`, `runWith_take_inWindow` and
    `inWindow_of_coreSum_eq`;
  - InputAccess (1): `Complexity.LogProg.access_width_half`;
  - DAGCircuitSat (2): `BoolCircuit.DAGCircuit.eval_tseitinGates_values` and
    `values_getD_eq_of_eval_tseitinGates`.
- New or moved in (11):
  - ConfigGraph (3): `Turing.Cfg.InWindow.core_bounds`,
    `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin` and `Turing.outSummary_eq_empty_iff`;
  - InputAccess (6): `Complexity.LogProg.arm_chain`, `boundedDecodeStride_loop` and `drop_canon`,
    and `Complexity.indicator_inputBitLang`, `indicator_inputLenLang` and `pairEncode_getD_snd`;
  - PolyTimeBlockLoop (1): `Complexity.length_pairEncode_drop_le`;
  - QBF (1): `Complexity.QBF.prefixTruth_congr_agree`.
- Name screen: 0 clashes.

**(c) Public removals: 7, all in Hydroxyi's files.** No stale use remains.
- `Complexity.Codec.InWin` (Word);
- `Complexity.Codec.outSummary_eq_empty_iff` (Checks; moved);
- `Complexity.Codec.inWin_runWith_take` and `mem_of_acceptsWithin` (Bridge);
- `Complexity.ExpBFS.inWin_of_coreSum_eq` (Radius);
- `Complexity.TQBFHard.values_getD_eq_of_eval_tseitinGates` (TQBFHardTseitin; D4);
- `Complexity.TQBFHard.prefixTruth_congr_agree` (TQBFHardSemantics; moved).

**Private removals: 64.**
- ConfigGraph 13: the 11 `s1b_*`, `InWindow` and the bridge;
- Bridge 4;
- QueryReshape 1 (`drop_canon`, moved);
- TQBF 46: the 45 `b4m*` and `codec_core_window`.

**Everything else.** Every other public statement of the 27 files is byte-identical modulo
whitespace. 41 proofs change, all listed in `edits.BODY`, plus 7 bodies that change by the D1
rewrite alone. Imports change only in VWord (+`TCSlib.Programs.Util.List`).

## 5. Checks (`logs/verify.log`: 60 of 60 PASS)

1. **Source precheck**, with a negative control: a mirror of the export without
   `Codec/Word.lean` makes precheck and land exit 2 and write nothing.
2. **Patches.** The 27 patches replay byte for byte, and the 4 comment-only files keep their code.
   The repository's tracked status is identical before and after the run. Another session added
   one untracked file, `audits/diagonal-p1-statements-findings.md`, during the run; it is reported,
   and none is under `TCSlib/` or `scripts/`.
3. **Elaboration.** The MIG-1 cut method is extended to restatements (`cuts.py`):
   - A changed module whose upstream changes are additive gets those modules' **deltas**: their
     new public declarations, copied from the landed files (identity asserted), and VWord's new
     import.
   - Every module downstream of a D1-restated module is **inlined**, changed or not, because its
     snapshot olean is stale.
   - Results:
     - All 27 changed modules elaborate with 0 errors.
     - Four **consumer cuts** cover the D1 consumers that no changed module's cut reaches:
       `ExpTime`, `ImmermanSzelepcsenyi`, `Savitch` and the `ClassPSPACE` facade.
     - Sorry warnings match the expected count everywhere: 21 in TQBF's closure, 2 in Savitch's.
     - The changed modules' sorried declarations are 21 at the base and 21 landed; none was
       deleted.
     - Every inlined region's warnings equal its base's; no new warning anywhere.
   - **The facade is elaborated as its own text.** Its 38-module cut fails for the base texts
     exactly as for the landed ones. The union of imports exposes `Complexity.LogProg.Mem`
     (`Machines/MARM`) inside `ISCountGenWalk`. The artifact control records the identical error
     sets.
   - Negative controls FAIL as required:
     - the landed Checks alone against the snapshot;
     - a mutated Word cut;
     - the Engine cut without InputAccess' delta.
4. **Freeze and API delta**, as in §4. Every allowance must be used. Controls C1–C9 each FAIL:
   - C1: a non-rewrite restatement;
   - C2: a public statement outside D1;
   - C3: an unauthorized removal;
   - C4: an unauthorized promotion;
   - C5: a proof change;
   - C6: a docstring change in DAGCircuitSat;
   - C7: an addition;
   - C8: a deletion not made;
   - C9: an import.
5. **Ledger map**, in `ledger-map.md`.
6. **Names, axioms, lint, widths and hygiene:**
   - names: 0 clashes, 0 stale uses, and no added reference to another file's private
     declaration; the name control FAILs as required;
   - axioms: 990 declarations printed, each on the standard three plus `sorryAx` only where the
     base already had it; no new `sorryAx`;
   - lint: no new FAIL (24 and 24); the WARN changes are only the size lines of TQBF, InputAccess
     and QueryReshape;
   - widths: 0 added lines over 100 columns;
   - hygiene: 0 hits.
7. **Replay list**, in §6.

## 6. Replay list

- **Size.** 119 modules: the 27 touched and 92 downstream, in topological order (asserted).
  - The root `TCSlib` is downstream but not listed.
  - Every import is listed, or has an olean in `oleans-ltip3` or the packages.
- **Colleague-owned modules.** It includes the downstream of `DAGCircuitSat` and
  `PolyTimeBlockLoop`: CircuitComplexity's CKT-SAT, Karp–Lipton and Meyer chains, PolyHierarchy,
  and so on. They are replayed, not edited.
- **In-flight landings.** No touched file and no replay-list member is a file of MIG-1 stage S,
  C1-A round 2 (now merged as #97) or G2–G4.

## 7. Recommendations

- **Radius' window lemmas** (accepted by the user as a follow-up). Not moved in this PR. Moving
  them would make CfgRecord, 5.3k lines with a large downstream, a touched module, and they are
  not copies.
  - `inWin_init` is now literally `Cfg.inWindow_init _ x s`: retire it in a follow-up.
  - `inWin_mono` belongs beside the predicate, as `Turing.Cfg.InWindow.mono` in CfgRecord.
  - `inWin_stepWith` is NDTM-specific and belongs in ConfigGraph, beside
    `NDTM.inWindow_of_coreSum_eq`.
- **ConfigGraph's imports.** After the s1b deletion `Constructible` may be unused; `RecordTable`
  is still needed for `Cfg.InWindow`. Imports were left unchanged; a pruning would need its own
  replay.

## 8. Open questions

None from this landing. The first pass's five questions are decided (§3).
