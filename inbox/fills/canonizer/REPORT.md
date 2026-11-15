# Fill canonizer — checkpoint 1 (the readers)

**Unit** `canonizer` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/canonizer` (local), checkpoint commit
`7064488bad9323cf3eb8d45faa9fcf328a8e5b99` · **Lean** 4.25.0, Mathlib at the base's manifest.

**Target status at this checkpoint:** `exists_canonizerExp` is still `sorry`. This checkpoint
delivers the two `rfl` readers of the brief's checkpoint 1, under Seyoon's scope pre-approval, and
the seal probe showing that each is needed. (The helper module and the proof are written and
compile locally; they come with the final delivery.)

## 1. Environment (addendum v1)

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

## 2. The readers (frozen files, pre-approved)

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

## 3. Next (final)

The helper `TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean`: `exists_codeCanonizer`
(the canonizer's specification transported along the two readers) and
`exists_effectiveMachineCode_canonizerTime_le` (the scheme `⟨CodeTM.serialize, codeDecode,
codeDecode_serialize_pad⟩` with `canonizerTime n = d · (n + 1)^d ≤ d · 2^{d n}`); then
`exists_canonizerExp := ⟨c, d, d, h⟩` and the docstring updates.

## 4. Scope requests

None sent: the only frozen-file changes are the two pre-approved readers.

## 5. Evidence at this checkpoint (`evidence/`, manifest `evidence/SHA256SUMS`)

- `logs/`: `preflight.log`, `source-sha256.log`, `order.txt`, `mathlib-roots.txt`, `cache-store.log`,
  `cache-get.log`, `packages-check.log`, `cache-probe.log`, `bootstrap.log`, `census-bootstrap.txt`,
  `census-bootstrap-vs-base.diff`, `cp1-probe-plain.log`, `checkpoint1-checks.log`,
  `checkpoint1-axioms.log`, `checkpoint1-width.log`, `checkpoint1-searches.log`, `base-lint.log`,
  `base-lint-turingmachine.log`, `checkpoint1-lint-turingmachine.log`, `checkpoint1-repro.log`
  (`git am` of the series at the base, in a scratch clone, with the committer data of
  `patches/COMMITS.tsv`: every hash reproduced).
- `probe-cp1/`: the four sealed runs of the probe (`.jsonl`, raw `.out`) and `sources/` (the sealed
  copies).
- `probes/`: `CacheProbe.lean`, `ReaderNeed.lean`, `AxiomsCP1.lean`.
- `scope-request/pre-approval.md`.
- `tools/`: the scripts used.

The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/canonizer/` except itself.
