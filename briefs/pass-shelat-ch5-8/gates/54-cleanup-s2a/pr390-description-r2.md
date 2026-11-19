Cleanup Stage 2, job S2-A (in-house): the ruled Rule-10 readers, seal fixes and body/header repairs that let the Pass–shelat owners of jobs J0 (foundations), J1 (Complexity hosts and derandomization) and J2 (the Asymptotic layer) pass the canonical seals without unfolding another file's definitions.

- Plan: `briefs/pass-shelat-ch5-8/cleanup-stage2/s2a-workplan-r1.md` and `s2a-items.tsv` (435 rows).
- Rulings: Q-A1..Q-A11 in `briefs/pass-shelat-ch5-8/cleanup-stages.md`; the batch rulings Q-D1-1..3, Q-D2-1..6 and Q-D3-1/2 in the decision log `PassShelatChapter5-8Plan.md`.
- Batch reports: `s2a-d1-report.md` … `s2a-d4-report.md` in the same folder.
- Gate: Gate 54 (Codex, cloud), `briefs/pass-shelat-ch5-8/gates/54-cleanup-s2a/`.

## Scope
- Base `61a5f0fb640622c15fdd33df56efa470b2bf26c8` (the merge base with the records branch); head `9f7f409c2e09749428db75b9ddd324f92695e4af`.
- 43 signed commits, one per work-plan step (A01–A38, A30 in two parts) plus four for the batch-D4 rulings:
  - Q-D2-1: the reader `epsClose_iff`;
  - Q-D2-3/Q-D3-1: five proof sketches and `OneWayYao.lean` under 1,000 lines, docstrings only;
  - Q-D2-4: the private `invProbAt_glPad_eq` in place of the twice-written local `hbridge`;
  - Q-D2-5: explicit `rawCollisionInputs_fst`/`_snd` in place of `@[simps!]`, same names and statements.
- 63 files, all under `TCSlib/`, +1,650 / −897. They are the 61 owner files of the plan, plus `Games/BitCodec.lean` (Q-A6 b) and `InformationTheory/Extractors.lean` (Q-D2-1).
- **Rows:** every S2-A row is done. The open items are size findings, and they belong to Stage 3 (Q-D2-3, Q-D3-2): `OneWay` (1,095 lines), `Factoring` (1,924), and `Collections` (1,177), which was already over the limit at the base.
- **Public API** (decls2, base vs head):
  - **41 added:** the planned readers and promotions, the DL-55 move's new home, `epsClose_iff` and the two explicit field lemmas.
  - **15 changed:**
    - DL-59's `Type*` widening of `Games.extTape` and three of its lemmas;
    - DL-35 #1/#3;
    - the Q8 freeze-exception restatements;
    - Q-A3's `glPad_f` and `glBit_append`.
  - **4 removed:** `host_dispatch`, `host_branch`, `host_halt`, and the DL-55 move's old home.
  - **Every row is mapped to a ruled item**, and there is no unplanned public declaration.
  - **Private changes:**
    - five private headers restated as ruled;
    - `oddParam_eval` and `invProbAt_glPad_eq` added;
    - `fac_ofFn_halves` deleted (DL-38).
  - **Definition bodies:** the 15 Q-A2 bodies are changed by casts only.

## Checks (in-house, olean replays; no `lake build`)
- **Batch replays.** Each batch replayed on a hard-link copy of the previous batch's tree, starting from snapshot #10. The D4 replay built 288 modules and reused 1,159. Every module had rc 0 and no errors, and the state check is OK over 1,447 modules.
- **Merged-tree replay** (`gates/54-cleanup-s2a/verification-r1.md`). This is the merge with the records tip `8836292693d7c611ee375d162f34766841635337`.
  - The merge (`git merge-tree`) is clean, with `TCSlib` tree `73af3ec6`.
  - The replay used a hard-link copy of the D4 tree. It built 28 modules and reused 1,428. All 28 had rc 0 and no errors, including root `TCSlib` and both `audits/*/Checks`.
  - The state check is OK over 1,456 modules.
- **Admissions.**
  - S2-A: 192 in 44 modules, byte-identical to the base, with no new `sorry`, `native_decide` or axiom.
  - Merged tree: 207 in 50 modules. The extra 15 in 6 modules are the records side's admitted GSW 6b targets, and the census is identical to the records tip's.
- **Q-A2 `rfl` probes.** All 15 changed definition bodies are `rfl`-equal to their originals, and the negative controls fail.
- **Seals** (coe-A canonical, plus coe-B).
  - Every S2-A owner gives 0 errors at its last seal (in the batch that last changed it), apart from three disclosed residues, none of them S2-A's:
    - `TrapdoorPredictor` 2: S2-B's rows;
    - `TuringMachine/Encoding` 4: a handed-off file;
    - downstream `FromPermutation`, 2 (coe-A) / 19 (coe-B): job J3's rows, unchanged across batches.
  - On the merged tree, coe-A gives 0 on the 10 D4 owners, and `FromPermutation`'s residue is unchanged.
- **Lint.**
  - `campaign_style_lint --check8b`: the FAIL count is unchanged. Merged against the records tip, WARN goes Complexity 390 → 389 and Cryptography 103 → 104 (the new `OneWay` size WARN). The other WARN changes are line counts and check-8/8b lists that shrink.
  - `style_lint`, on the 75 files the merge changes against the base: one new finding, `OneWay` over 1,000 lines (Stage 3).

## Disclosures
- **`ofFn_chunk`** is kept and re-proved, as the plan's fallback allows.
- **Step A30** grew to about +187 lines, against the plan's ~70, because of local 2n-bit bounds in `fac_strong_key` and `exists_plantFactorer`.
- **`rawCollisionInputs_fst`/`_snd`** are no longer `rfl` lemmas. Like the generated ones, they are not `@[simp]`. Nothing in the library uses them.
- **Old duplicate `dbl_append`** (DL-62): ledgered for Stage 3.
- **Consumer-side copies:** S2-B and S2-D remove the copies left by the promotions (DL-56, DL-57, DL-59).
- **Signatures:** the 43 commits carry SSH signatures from the account's shared Claude key; none was verified.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
