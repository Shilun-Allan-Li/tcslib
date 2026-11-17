# make_report.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. Writes REPORT.md: the fixed narrative (base, pins,
# preflight, tree, who did what, tool changes, method, questions) with figures read from the evidence, then the tables of
# report_tables.py. Usage: python3 -I make_report.py <delivery-dir> <checkpoint|final> <n>
import sys, os, json, subprocess, csv, re, collections
dl, mode, n = sys.argv[1:4]; ev = os.path.join(dl, 'evidence')
def rd(p): return open(os.path.join(ev, p), encoding='utf-8').read()
pre = rd('logs/preflight.log'); mapsha = rd('build/olean-tree-map.sha256').split()[0]
pk = rd('logs/pkgcheck.log').strip().split('\n')[-1]
cache = [l for l in rd('logs/cache-get.log').split('\n') if 'Attempting' in l or 'Decompressing' in l or l.startswith('rc=')]
store = rd('logs/cache-store.log').strip().replace('\n', '; ')
summ = rd('build/summary.txt').strip().split('\n')[-1].lstrip('# ')
own = rd('ownercheck/summary.txt')
loc = collections.Counter(l.split('\t')[6].strip() for l in rd('locate/locate.tsv').split('\n')[1:] if l)
restore = rd('build/restore-check.txt').strip() if os.path.exists(os.path.join(ev, 'build/restore-check.txt')) else '(at the final)'
mem = [l for l in rd('logs/memsample.log').split('\n') if l]
mins = min(int(re.search(r'avail_kB=(\d+)', l).group(1)) for l in mem); maxl = max(int(re.search(r'lean=(\d+)', l).group(1)) for l in mem)
maxanon = max([int(a) for l in mem for a in re.findall(r'anon=(\d+)', l)] or [0]); maxrss = max([int(a) for l in mem for a in re.findall(r'rss=(\d+)', l)] or [0])
tables = subprocess.run(['python3', '-I', os.path.join(ev, 'tools/report_tables.py'), dl], capture_output=True, text=True, check=True).stdout
qs = open(os.path.join(ev, 'tools/questions.md'), encoding='utf-8').read()
txt = f"""# DW-10 seal-debt inventory (`dw10-seal-inventory`): {'checkpoint ' + n if mode == 'checkpoint' else 'final'}

Lead: Claude (cloud worker). {'**Checkpoint ' + n + '**: see *Scope of this checkpoint* below; the final follows.' if mode == 'checkpoint' else ''}
The job is checks only: no file under `TCSlib/`, `audits/`, `scripts/` or the lakefile was changed, no Lean branch was created
or committed, no PR was opened; there are no `patches/` or `src/`. Every Lean probe ran through `scripts/lean_check_tree.sh`
(the bootstrap) or `evidence/tools/seal/runner_full.py` (`lean -DmaxErrors=0`, no `-o`).

## Base, pins and environment

| Item | Value |
|---|---|
| Issue base | `f472accd5e000a53d0fbe02b5414435429ce4a70` (an ancestor of the records tip) |
| Lean equality | `git diff --quiet a6d01b1bd1a92e2ac0be9999689467fea7e4e77b f472accd5e000a53d0fbe02b5414435429ce4a70 -- TCSlib TCSlib.lean audits lakefile.lean lake-manifest.json lean-toolchain` exits 0; `TCSlib` tree `06b51ea90a9a0ef49e1dc3e7034ba32ec9b75fe6` at both |
| Records tip used (`cryptography/pass-shelat-ch2-4`) | `cbc44b6e4ff3036860a77cc6a1c3bca0b0d33428`; no `.lean`, `lean-toolchain` or `lake-manifest.json` change after the base. Records pin of the prompt `4367db3c9f3c0b4dd81117ab001e6707aa42c0c5`: `issued-r1/` equals the pack (plus `dispatch.md`); all 21 record hashes of the brief verified |
| Exchange tip used | `d4cfd2f893fb9b448c5d997f037d6ba055cbc031` (the pack: `shasum -a 256 -c SHA256SUMS` 21/21 OK) |
| `main` | `a954201d421a61994e02e36ff3cf4b16dce53f5d` at the start (`workflow.md` §6 read there); `b986b8620fc6117034462212df7070c80a79ff65` after #353 (§4.1 *Lean parallelism*) |
| Toolchain | Lean 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), Lake 5.0.0-src+cdd38ac, installed by elan |
| Mathlib | `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` (manifest); package check: {pk} |
| Cache | narrowed `lake exe cache get` on the 119 roots (`roots.txt`, recomputed and equal): {'; '.join(cache)}. Store before the fetch: {store} (all archives fetched by this session). 0 empty oleans; root probe `import Mathlib.Algebra.BigOperators.Field` rc 0 |
| Preflight | nproc 4; cgroup v1 with no memory limit, so headroom = MemAvailable 15.12 GiB (floor 4 GiB); disk 25.32 GiB free on ext4 `/dev/vda` (floor 12 GiB). A first attempt measured 11.39 GiB with the lead's full worktrees (logged with a wrong `PASS` label, annotated in `logs/preflight-attempt1.log`); the lead's own worktrees were made sparse and the preflight re-run passed before any cache or Lean work |
| Bootstrap | `order.txt` (613 modules) one module at a time: {summ}; every source equals `SOURCE-SHA256SUMS` (`build/summary.txt`) |
| Olean tree | 613 `.olean`, map `build/olean-tree-map.txt`, SHA-256 `{mapsha}`; made read-only (uid 0 bypasses the mode bits: `build/readonly-note.txt`); restore check: {restore} |

## Parallelism (user override and ruling, 2026-11-17)

The brief's "one Lean process at a time on the host, through one lock" was overridden by the user during the run ("I'm overriding
the 'one Lean process at a time on the host' rule ... Be mindful of making sure each Lean process has enough memory"), then by
Seyoon's ruling (`workflow.md` §4.1 *Lean parallelism*, main #353): cloud workers run a pool of at most nproc Lean processes,
keeping about 2 GB (15%) available. Before the override, the bootstrap, the collectors, the scan kinds probes, the locator, the
first 12 seal probes and the first controls pretest ran strictly one at a time. Afterwards the seals ran in a pool of 4 workers
(lock slots w1..w4 as the counting semaphore; claim files so no probe runs twice; a probe starts only when MemAvailable is at least
4.5 GiB): `seals/PARALLEL.txt`. Measured (30 s samples, `logs/memsample.log`): at most {maxl} Lean processes at once, minimum
MemAvailable {mins / 1048576:.1f} GiB, peak private (anonymous) memory of one Lean process {maxanon / 1024:.0f} MiB, peak RSS
{maxrss / 1048576:.2f} GiB (mostly shared olean mappings). The running seal phase was not interrupted to switch over (the ruling's
instruction); the pool is recorded per phase in `seals/PARALLEL.txt`.

## Who did what

{rd('../evidence/tools/whodid.md') if os.path.exists(os.path.join(ev, 'tools/whodid.md')) else 'The lead did everything at this checkpoint (no sub-agent has run).'}

## Method and tool changes

The suite is the bb1-sim adaptation (exchange `d929cc21ec817b2518d57a7262e42744728f029a`, tree `e25f7bf0c9b78e764917868ad52a5f4044d0dcd2`) and
DW-5's (`dw5-evidence.zip`, `12abc05a…`, verified), copied into `evidence/tools/`; every change is recorded in the tool's header.
The archived Gate 06/10 instrumenter (`seal/review/archived-gate10-tools/`) is unmodified (`archived-gate10-tools.SHA256SUMS`).
- **Collectors** (`collect/b1..b5`, 87/87/87/87/86 owners in build order, `collect/batches.tsv`): `NmCollect.template.lean`
  adapted to add COEINST records (the one coercion instance found is `TCSlib.InformationTheory.FinDist.instCoeFunForallReal`),
  ROOT flags and own-module type references (owner check, controls) and ROOT `eqn_refs` (check 5). All rc 0, 0 errors.
- **Seals**: `mkseals_ab.py` / `mkseals_coe.py` unchanged, `SEAL_CHUNK=2000` for every probe. Variant deduplication
  (`tools/qbuild.py`): coe-A always runs; strict-A when its bytes differ from coe-A; B when it differs from A after the label
  normalization `SealB_` -> `SealA_` (the labels differ by construction, so byte equality is checked after that normalization; both
  SHA-256 values are in `seals/dedup.json`). Request counts reproduce the recorded ones exactly (IterateFind 595, ModuleHost 241,
  IterateFindHost 251, Yao coe-A 3,046). `tools/sealtab.py` maps every error to its source line and declaration and checks
  every install/EOF record (requested = verified, summed over chunk parts).
- **Scan**: `scan1_g40.py` + archived `scan_explicit.py` + `scan2.py` unchanged, `touched.py` with the empty tree as base (every
  declaration touched). The kinds probe of batch b2 overflowed Lean's stack (137k candidate names in one string literal, rc 134;
  kept as `scan/b2-attempt1/`); b2 ran as b2a/b2b. The archived lexer inventories `unfold`, `delta`, `rw`/`rwa`/`erw`/`nth_rw`,
  the `simp` family, `norm_num`, `field_simp`, `push_cast`; `show`/`change` reads are definitional and are caught by the seals
  (DW10-W4).
- **Item location** (`locate/`): every input item's name resolved in the elaborated environment (handed-off files included):
  {dict(loc)}; the 9 not found are exactly the NO-DECLARATION rows (attempt 1 queried private names verbatim; kept).
- **Generated-equation reads** (`eqrefs.tsv`): from the collectors' `eqn_refs` (`eq_<n>`, `eq_def`, `eq_unfold`, `splitter`).
- **Controls** (`controls/`): `tools/mkctl_dw10.py`, one pair per owner, 20 harnesses of up to 25 owners, unsealed pretest first
  (attempt 1 stopped after a 48-minute unbounded `rfl`; attempt 2 bounds every control body by `maxHeartbeats 400000`).
- **Reader index** (`readers/`): every TCSlib theorem `<P>_*` (or lower-camel) whose type mentions a definition P; the classification
  uses as published readers `_eq`, `_def`, `_apply`, `_iff`, `_eq_def` and run/contract lemmas.
- **Reconciliation** (`tools/reconcile.py`, matching rules in its header) and the report (`tools/report_tables.py`, this file).

## Owner check (Checks, step 2)

```
{own.strip()}
```

{'## Scope of this checkpoint' + chr(10) + chr(10) + rd('../evidence/tools/scope.md') if mode == 'checkpoint' else ''}

## Totals and lists

{tables}

## Questions for Seyoon

{qs}

## Evidence

`evidence/SHA256SUMS` lists every evidence file; the top-level `SHA256SUMS` every delivered file. Large directories (collector logs,
seal records and probe sources, seal logs, scan inputs, control harnesses and logs) are in `evidence/zip/<name>.partNN.zip` (at most
90 MB each) with `<name>.partNN.entries.txt` (path, bytes, SHA-256 of each uncompressed file).
"""
open(os.path.join(dl, 'REPORT.md'), 'w', encoding='utf-8').write(txt)
print('REPORT.md', len(txt))
