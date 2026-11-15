# Fill canonizer — final

**Unit** `canonizer` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/canonizer` (local), head `ba7096e8e` ·
**Lean** 4.25.0, Mathlib at the base's manifest.

## 0. Status

| Target | Status |
|---|---|
| `TCSlib.Cryptography.exists_canonizerExp` | **proved**; statement unchanged; axioms `[propext, Classical.choice, Quot.sound]` |

Commits (the series in `patches/`, with `patches/COMMITS.tsv`):
1. `7064488ba` checkpoint 1 — the two `rfl` readers (pre-approved scope; exchange `3d65c2466`);
2. `ba7096e8e` `exists_canonizerExp` proved.

The headlines of `Universal.lean` (`fUniversal_easy`, `fUniversal_hard`, `fUniversal_weakOneWay`,
`theorem_63_1`) are unchanged and still take `CanonizerExp c` as a hypothesis; now the hypothesis
is known to be satisfiable. The final sweep of the supplied order with the helper inserted before
the owned module has 0 errors, and the sorry census is `base-sorries.txt` minus
`exists_canonizerExp` (§6).

## 1. The proof

- **The readers (checkpoint 1).** `Turing.MachineFormat.exists_polyCanonizer` at
  `Turing.oneTapeMachineFormat` gives `C, d` with `C` computing
  `α ↦ oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α)` in time `n ↦ d · (n + 1)^d`
  on every input. The two pre-approved readers turn that function into
  `α ↦ (codeDecode α).serialize` (`oneTapeMachineFormat_serialize_decode`, then
  `oneTapeFormat_serialize_decode`); without them this step needs unfolding `oneTapeMachineFormat`,
  `oneTapeFormat` and `codeDecode` (the seal probe, §8.2).
- **The helper** (`TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean`, 82 lines):
  `exists_codeCanonizer` (the transported canonizer) and
  `exists_effectiveMachineCode_canonizerTime_le`: the effective machine code
  `⟨⟨CodeTM.serialize, codeDecode, codeDecode_serialize_pad⟩, C, fun n => d · (n + 1)^d, hC⟩` (the
  scheme of `Turing.exists_uniformMachineCode`, with its time bound visible), and
  `d · (k + 1)^d ≤ d · 2^{d k}` from `k + 1 ≤ 2^k` (`Nat.lt_two_pow_self`), `pow_mul` and
  `Nat.pow_le_pow_left`.
- **The target** (owned file): `obtain ⟨c, d, h⟩ := exists_effectiveMachineCode_canonizerTime_le;
  exact ⟨c, d, d, h⟩` (`CanonizerExp` is the owned file's own definition, `A = B = d`).

**Edge cases.** `k = 0`: `d · 1^d ≤ d · 1`. `d = 0`: both sides are `0`. Malformed codes: the time
bound of `exists_polyCanonizer` holds on every input, and `codeDecode` sends a malformed string to
the fallback machine, whose serialization is the canonizer's output. The axioms of
`exists_polyCanonizer` are standard (`[propext, Classical.choice, Quot.sound]`; the chain uses
`FinTM.computesFunInTime_appendBit`, not the admitted `appendBitTM_computes`, as the brief's text
trace expected — confirmed by the print, `logs/checkpoint1-axioms.log`, `logs/final-axioms.log`).

## 2. Changed and new files

| File | Lines (base) | Change |
|---|---|---|
| `TCSlib/Cryptography/Asymptotic/Universal.lean` (owned) | 955 (945) | the proof; docstrings; import; six pre-existing long lines wrapped |
| `TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean` (new) | 82 | the helper |
| `TCSlib/Complexity/TuringMachine/CodeFormat.lean` (frozen, pre-approved) | 600 (595) | reader `oneTapeFormat_serialize_decode` |
| `TCSlib/Complexity/TuringMachine/CodeSimulator.lean` (frozen, pre-approved) | 9133 (9126) | reader `oneTapeMachineFormat_serialize_decode` |

**Owned-file edits.** The module title has no "(statement phase)" at the base (unchanged). The
encoding-deviation paragraph now ends: some scheme satisfies the hypothesis
(`exists_canonizerExp`, proved from `exists_polyCanonizer`), so the conditional headlines apply to
it. `## Main results`: `exists_canonizerExp` — some scheme satisfies `CanonizerExp` (proved,
run-3 audit P3-4 closed). New `## Contents` naming the helper. The target's docstring is no longer
"Open problem": it states `∃ c, CanonizerExp c` with its formula and a `[PS10, §2.13]` tag, and the
superseded `Build/` sketch is replaced by the delivered proof (the brief: "The docstring's sketch is
superseded"). One import (`Universal.Canonizer`). Six pre-existing lines over 100 characters
(lines 200, 661, 724, 759, 899, 900 of the base) were wrapped, whitespace only, so that every line
of the owned file is within 100 characters (`logs/final-width.log`); no declaration, statement or
proof step changed. The conditional headlines, every other declaration, the statement prose and
the simp attributes are unchanged.

## 3. New declarations

- `TCSlib.Cryptography.exists_codeCanonizer` (helper): `∃ (C : FinTM Bool) (d : ℕ),
  C.ComputesFunInTime (fun α => (codeDecode α).serialize) fun n => d * (n + 1) ^ d`.
- `TCSlib.Cryptography.exists_effectiveMachineCode_canonizerTime_le` (helper):
  `∃ (c : EffectiveMachineCode) (d : ℕ), ∀ k, c.canonizerTime k ≤ d * 2 ^ (d * k)`.
- `Turing.oneTapeFormat_serialize_decode` (`CodeFormat.lean`) and
  `Turing.oneTapeMachineFormat_serialize_decode` (`CodeSimulator.lean`): the two readers.

Each has a formula docstring; no `@[simp]`, no new `def` or `abbrev`.

## 4. Overlap and reuse

| New declaration | Nearest relative (`path:line`) | Relation | Why not reused |
|---|---|---|---|
| `exists_effectiveMachineCode_canonizerTime_le` | `Turing.exists_uniformMachineCode` (`Complexity/Diagonalization/EXPCOM.lean:156`) | the same effective part (`CodeTM.serialize`, `codeDecode`, `codeDecode_serialize_pad`, the polynomial canonizer, `canonizerTime n = d (n+1)^d`) | it is stated as `Nonempty UniformMachineCode`, which hides the time bound; and its proof matches the canonizer's type by unfolding `oneTapeMachineFormat`/`oneTapeFormat`/`codeDecode` (Rule 10). The construction is repeated through the readers, with the bound exported |
| same | `Turing.exists_effectiveMachineCode` (`Complexity/TuringMachine/MathlibBridge.lean:1162`), `exists_effectiveMachineCode2` (`Codes2Tape.lean`) | other effective codes | no time bound on their canonizers |
| `exists_codeCanonizer` | `Turing.MachineFormat.exists_polyCanonizer` (`CodeSimulator.lean:8364` at the base) | its specialization at `oneTapeMachineFormat`, read through the readers | reused, not re-proved |
| `oneTapeFormat_serialize_decode` | `Turing.codeCanonical_eq` (`CodeFormat.lean:592`) | `codeCanonical xs = (codeDecode xs).serialize`; another reading of the same canonical serialization | relates `codeCanonical`, not `oneTapeFormat.serialize ∘ oneTapeFormat.decode` |
| `oneTapeMachineFormat_serialize_decode` | none | the `MachineFormat` view of `oneTapeFormat` | no lemma relates the two structures' projections |
| (inline) `(k + 1)^d ≤ 2^{d k}` | Mathlib `Nat.lt_two_pow_self`, `Nat.pow_le_pow_left`, `pow_mul` | a three-step consequence | no stated lemma found; kept inline |

Searches: `logs/checkpoint1-searches.log` (the readers' statement shapes and names,
`exists_polyCanonizer`, `canonizerTime :=`, `CanonizerExp`) and `logs/final-searches.log` (the
helper's statement shapes, the scheme literal, `(k + 1)^d ≤ 2^…`, Mathlib's power lemmas).

## 5. Scope requests, promotion and reader requests

**Scope requests:** none sent. The two readers are Seyoon's pre-approval of 2026-11-14 (verbatim in
`evidence/scope-request/pre-approval.md`), delivered exactly as approved: `rfl`, beside their
definitions, formula docstrings, no attribute. No other frozen file was touched.

**Promotion requests:** none (the helper's two theorems are specific to this file's hypothesis).

**Reader requests:** none beyond the two pre-approved readers.

## 6. Checks (final)

All Lean runs one process at a time, one module per `scripts/lean_check_tree.sh` call (via
`tools/check.sh`); post-sweep runs by `tools/final_pipeline.sh` (step log
`logs/final-pipeline.log`). No host restart during the runs.

- **Recheck and sweep** (`logs/final-sweep.log`, 03:09–03:25 UTC): the 184 modules of
  `logs/order-with-helpers.txt` (`order.txt` with the helper inserted before the owned module),
  each checked from scratch, in order: **184/184 status 0, no `error:`/`error(…)` line**. The only
  warning in the changed files is the base's `unused variable hc` in `fUniversal_hard` (line 797 at
  the base, 805 now).
- **Sorry census** (`logs/final-census.txt`, `logs/final-census-vs-base.diff`): 18 declarations in
  8 modules; the diff against `base-sorries.txt` is exactly
  `TCSlib/Cryptography/Asymptotic/Universal: 1: exists_canonizerExp` and the total (19 → 18).
- **Axioms** (`logs/final-axioms.log`, `probes/AxiomsFinal.lean`): `exists_canonizerExp` depends on
  `[propext, Classical.choice, Quot.sound]`. All **1077 stored constants** of the four changed and
  new modules (Universal 67, Universal.Canonizer 2, CodeFormat 122, CodeSimulator 886; auxiliary
  constants included) use only `{Classical.choice, Quot.sound, propext}`; no `sorryAx`.
- **Whole-file seals** (`seals/`; `tools/seal_gen.py`, `seal_run.py`, `seal_all.sh`; variants
  **A**/**B** = `PolyExpr.eval` excluded/sealed, each **strict**/**coe** = projection coercions
  sealed/notation; the runner counts `error:` and `error(…)` and keeps every raw `.out`):
  - **the helper** `Universal/Canonizer.lean`: 0 errors in all four variants;
  - **the owned file** `Universal.lean`: final = base in every variant (A: 10 errors in
    `clockedAnswer_eq_cons_of_computesInTime`, `clockedAnswer_eq_false_of_not_computesInTime`,
    `invProbAt_reduction_ge`, `ofFn_getD_eq_take`; B adds `eval_univOutLen`, `fUniversal_hard`:
    12). All are pre-existing; **the new proof of `exists_canonizerExp` does not fail**;
  - **CodeSimulator.lean**: final = base in every variant (101 errors in 48 pre-existing
    declarations, listed in `seals/seals-compare.log`); the reader
    `oneTapeMachineFormat_serialize_decode` is not among them;
  - **CodeFormat.lean**: base 14 errors in `codeActionK_length`, `codeCanonical_eq`, `codeDecode`,
    `codeDecode_serialize_pad`, `oneTapeFormat`; final 16, the two new errors in the reader
    `oneTapeFormat_serialize_decode`. **Attribution:** a cascade of the pre-existing failure of
    `oneTapeFormat` itself under the seal (its field `serialize_assemble := … rfl` unfolds the
    foreign `CodeTM.serialize`, `Encoding.lean`); with `oneTapeFormat` broken, its own readers
    `codeDecode` and `codeDecode_serialize_pad` fail at the base exactly as the new reader does
    (`Type mismatch: oneTapeFormat.decode xs has type oneTapeFormat.Code but is expected to have
    type CodeTM`). The reader unfolds only its own file's definitions (`oneTapeFormat`,
    `CodeFormat.decode`, `codeDecode`), as Rule 10 allows beside a definition;
  - strict and coe agree in A and in B (`seals-compare.log`, last two sections).
  Base copies of the three files that exist at the base are in `base/` (sha256 equal to
  `SOURCE-SHA256SUMS`); every checked sealed copy is in `seals/sources/<tag>/`.
- **Paired controls** (`controls/`, `logs/controls-plain.log`, `seals/controls-*.jsonl`):
  `CtlUnfold` (`codeDecode xs = oneTapeFormat.decode xs := rfl`): unsealed 0, **1 error in each
  sealed variant**; `CtlEval` (`(PolyExpr.const 1).eval 5 = 1 := rfl`): unsealed 0, A 0, **B 1**;
  `CtlReader` (the two readers and `PolyExpr.eval_const`): 0 everywhere; `CtlCoe` (an explicit
  application of the projection coercion `FinDist.instCoeFunForallReal` by `rfl`): 0 everywhere, a
  documented probe, not a negative control: Lean reduces a projection of an instance even when the
  strict seal makes the instance irreducible, so no control can make the strict variant fail on a
  projection coercion. Each sealed negative fails exactly once; the positive passes.
- **Explicit-unfold scan** (`scan/`): Universal 90 rows, 0 foreign definitions (base the same);
  Canonizer 2 rows, both theorems (the readers); CodeFormat 6 and CodeSimulator 35 explicit unfolds
  of foreign definitions, **all pre-existing** (the same sets at the base: `scan/scan-compare.log`,
  "NEW foreign explicit unfolds: 0").
- **Lint** (`logs/base-lint.log`, `logs/final-lint.log`, `logs/final-lint-vs-base.diff`):
  `campaign_style_lint.py TCSlib/Cryptography --check8b`: 92 FAIL / 101 WARN at the base and at the
  final, **identical FAIL and WARN line sets**. On `TCSlib/Complexity/TuringMachine` (the frozen
  files' directory; `logs/base-lint-turingmachine.log`, `logs/final-lint-turingmachine.log`,
  `logs/final-lint-turingmachine-vs-base.diff`): the readers remove `oneTapeFormat` and
  `oneTapeMachineFormat` from the check-8 WARN lines, and CodeSimulator's size WARN reads 9133
  instead of 9126 lines (pre-existing, disclosed: the file is over 1000 lines at the base); no new
  FAIL or WARN line.
- **Width and size** (`logs/final-width.log`): the owned file and the helper have every line within
  100 characters and are within 1000 lines; the frozen files' added lines are within 100
  characters (their pre-existing long lines and CodeSimulator's size are reported, not changed).
- **Patch reproduction** (`logs/final-repro.log`): `git am` of each patch at the base in a scratch
  clone, with the committer data of `patches/COMMITS.tsv`, reproduces both hashes.

## 7. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

`evidence/SHA256SUMS` lists exactly the files under `evidence/`; the top-level `SHA256SUMS` lists
every delivered file under `inbox/fills/canonizer/` except itself (both verified by
`tools/manifest.sh` before the push).
- `logs/`: environment and bootstrap (`preflight.log`, `source-sha256.log`, `order.txt`,
  `mathlib-roots.txt`, `cache-store.log`, `cache-get.log`, `packages-check.log`, `cache-probe.log`,
  `bootstrap.log`, `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`, `base-lint.log`,
  `base-lint-turingmachine.log`); checkpoint 1 (`cp1-probe-plain.log`, `checkpoint1-*.log`); final
  (`order-with-helpers.txt`, `final-sweep.log`, `final-census.txt`, `final-census-vs-base.diff`,
  `final-axioms.log`, `final-lint.log`, `final-lint-vs-base.diff`, `final-lint-turingmachine.log`,
  `final-lint-turingmachine-vs-base.diff`, `final-width.log`, `final-searches.log`,
  `final-pipeline.log`, `controls-plain.log`, `scan-final.ids.log`, `scan-final.raw.log`,
  `scan-base.ids.log`, `scan-base.raw.log`, `final-repro.log`).
- `probe-cp1/`: the checkpoint-1 seal probe runs and their sealed copies.
- `seals/`: `{final,base,controls}-{A,B}-{strict,coe}.jsonl` and `.out`, `seals-compare.log`,
  `sources/<tag>/`.
- `scan/`: `scan-final.tsv`, `scan-base.tsv`, `scan-compare.log`, `sources/{final,base}/`.
- `controls/`: `CtlUnfold.lean`, `CtlEval.lean`, `CtlCoe.lean`, `CtlReader.lean`.
- `base/`: `UniversalBase.lean`, `CodeFormatBase.lean`, `CodeSimulatorBase.lean` (the changed files
  at the base).
- `probes/`: `CacheProbe.lean`, `ReaderNeed.lean`, `AxiomsCP1.lean`, `AxiomsFinal.lean`.
- `scope-request/pre-approval.md`.
- `tools/`: every script used.

`patches/`: `git format-patch 107f1e8c..ba7096e8e` (2 patches) and `COMMITS.tsv`; `src/`: the four
changed and new files at `ba7096e8e`.

## 8. From checkpoint 1

### 8.1 Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom
  is `MemAvailable` = 16491368448 B = 15.36 GiB; the clone's filesystem (ext4, `/dev/vda`) has
  16523374592 B = 15.39 GiB free (floor 12 GiB): `PREFLIGHT PASS`. To get there, the git worktree
  of this host's delivered `learning` fill (`/workspace/learn`, branch kept) and that fill's own
  scratch directories (`/tmp/learn-repro`, a patch-reproduction clone; `/tmp/lintbase`) were
  removed. No dependency tree was copied or moved.
- **Clone:** a new worktree `/workspace/canon` of the local repository, branch `fill/canonizer` at
  the issue base; its sources match `SOURCE-SHA256SUMS` (183 files, `source-sha256.log`).
- **Cache:** the store (`~/.cache/mathlib`, `cache-store.log`) held 2402 archives from this host's
  earlier fills. The narrowed `lake exe cache get` for the 80 roots (`mathlib-roots.txt`, the same
  list as `roots.txt`) downloaded 1 file, decompressed 2123 and exited 0 (`cache-get.log`). No
  zero-size olean; the probe importing `Mathlib.Algebra.BigOperators.Field` elaborates
  (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports them).
- **Bootstrap** (`bootstrap.log`): the 183 modules of `order.txt`, one `scripts/lean_check_tree.sh`
  call each (through `tools/check.sh`), in order: 183/183 status 0, no error, no host restart.
  Sorry census = `base-sorries.txt` (19 declarations in 9 modules; `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`: identical).

### 8.2 The readers and the seal probe

Seyoon's pre-approval (2026-11-14) is recorded verbatim in `evidence/scope-request/pre-approval.md`.
Exactly the two approved readers were added, each `rfl` beside its definition, with a formula
docstring and no attribute, stated between `List Bool` values:

- `TCSlib/Complexity/TuringMachine/CodeFormat.lean` (595 → 600 lines), after
  `codeDecode_serialize_pad`: `Turing.oneTapeFormat_serialize_decode (xs : List Bool) :
  oneTapeFormat.serialize (oneTapeFormat.decode xs) = (codeDecode xs).serialize := rfl`.
- `TCSlib/Complexity/TuringMachine/CodeSimulator.lean` (9126 → 9133 lines), after
  `oneTapeMachineFormat`: `Turing.oneTapeMachineFormat_serialize_decode (α : List Bool) :
  oneTapeMachineFormat.serialize (oneTapeMachineFormat.decode α) =
  oneTapeFormat.serialize (oneTapeFormat.decode α) := rfl`.

**The seal probe** (`probes/ReaderNeed.lean`, run at the base, before the readers existed):
three theorems closed by unfolding, which is how `Turing.exists_uniformMachineCode`
(`Diagonalization/EXPCOM.lean:156`) matches the canonizer's type:
`need_codeFormat` (the first reader's statement, by `rfl`), `need_codeSimulator` (the second's) and
`need_transport` (`exists_polyCanonizer`'s specification read as `α ↦ (codeDecode α).serialize`).
Unsealed the probe elaborates (`logs/cp1-probe-plain.log`, status 0). Under the whole-closure seal
in all four variants (A/B × strict/coe; `probe-cp1/probe-{As,Ac,Bs,Bc}.jsonl` and `.out`, sealed
copies in `probe-cp1/sources/`) it fails with **exactly three errors, one per theorem**
(`need_codeFormat`, `need_codeSimulator`, `need_transport`). So neither reader can be replaced by a
published lemma (none relates the two formats' serializations to `codeDecode`; searches in
`logs/checkpoint1-searches.log`), and each is needed: the first unfolds `oneTapeFormat` (and
`codeDecode`) of `CodeFormat.lean`, the second `oneTapeMachineFormat` of `CodeSimulator.lean`.
(The `PolyExpr.eval` exclusion is vacuous here: `PolyExpr` is not in this closure.)

Checks: `logs/checkpoint1-checks.log` (both files rechecked, status 0, no warning);
`logs/checkpoint1-axioms.log` (`probes/AxiomsCP1.lean`): the readers depend on standard axioms only
(`oneTapeFormat_serialize_decode`: `[propext, Quot.sound]`; `oneTapeMachineFormat_serialize_decode`:
`[propext, Classical.choice, Quot.sound]`), and so does `Turing.MachineFormat.exists_polyCanonizer`
(`[propext, Classical.choice, Quot.sound]`; the chain is standard, as the brief's text trace
expected).

**Width and size** (`logs/checkpoint1-width.log`): the added lines are all within 100 characters.
Both frozen files have pre-existing long lines (CodeFormat: 10 lines over 100 at the base;
CodeSimulator: 1), and CodeSimulator is over 1000 lines at the base (9126); the readers add 5 and
7 lines and no long line.

**Lint.** `campaign_style_lint.py TCSlib/Cryptography --check8b` at the base: 92 FAIL / 101 WARN
(`logs/base-lint.log`); this checkpoint changes no file under `TCSlib/Cryptography`. On the frozen
files' directory, `TCSlib/Complexity/TuringMachine` (`logs/base-lint-turingmachine.log`,
`logs/checkpoint1-lint-turingmachine.log`): the readers remove `oneTapeFormat` and
`oneTapeMachineFormat` from the check-8 WARN lines ("public def without a lemma beside it"), and
the size WARN of CodeSimulator now reads 9133 lines instead of 9126; no other line changes.

