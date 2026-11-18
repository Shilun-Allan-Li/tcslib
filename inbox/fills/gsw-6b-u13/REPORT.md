# Fill gsw-6b-u13 — final (GSW 6b unit U13, the decryption formula, G5–G8)

**Unit** `gsw-6b-u13` · **Worker** Claude (lead, alone; no sub-agents) · **Base** B6
`bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d` (tree `845bdc982fd8f79aba755796bb13188922c4655d`) · **Head**
`74fb355a17a47076d7de44a0f691ea03572cb170` (local branch `fill/gsw-6b-u13`, one commit) · **Records pin**
`bbc930b3853adb29ba96324568e984d521abd257` · **Lean** 4.25.0, Mathlib `029db123ddaa`.

**Status: final. All six targets G5–G8 proved**; no `sorry` in the owned file. The head is the one delivered at
checkpoint 1 (exchange commit `ab9d1ec3a…`); no Lean change since.

| Row | Target (`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.`) | Base line → head line | Status |
|---|---|---|---|
| G5 | `vecMul_secretVector_eq_sum` | 143 → 143 | proved |
| G6 | `decryptFormula_eval` | 165 → 170 | proved |
| G7 | `nandFormula_eval` | 176 → 200 | proved |
| G8 | `depth_nandFormula_le` | 188 → 213 | proved |
| G8 | `maxFanin_nandFormula_le` | 198 → 231 | proved |
| G8 | `decDepth_le` | 211 → 251 | proved |

All six: `[propext, Classical.choice, Quot.sound]`, no `sorryAx` (the trace is empty). No helper was added, public or
private; no import; no statement, header, prose, definition or reader changed; no `sorry`, `admit`, `native_decide`,
`axiom` or `opaque`.

## 0. Inputs and the missing rulings file (U13-W1)

- **`briefs/lattice-gsw/phase6/issued-6b-fills-r1/rulings.md` does not exist** at the pin `bbc930b3…`, nor at the
  records tip seen at delivery, and was never committed (`git log --all` on the path is empty;
  `logs/inputs-check.log`). The folder's `SHA256SUMS` does not list it either. The README (*Blocking*, item 2) says
  that U12 and U13 depend on none of the folder's questions (Q-6BF-1 to Q-6BF-7), so no ruling could change this
  unit's work; I proceeded on the brief, COMMON.md and dup-sweep.md, and record the gap as question **U13-W1** (§10).
  I did not treat it as E-INPUT, because no input hash differs; if Seyoon's rulings exist elsewhere and bear on U13,
  this delivery should be re-checked against them.
- **COMMON §1 inputs:** all 17 SHA-256 values match at the pin (`logs/inputs-check.log`). The folder verifies with
  `sha256sum -c SHA256SUMS` (43 files OK; paths equal, nothing missing or extra). Read: the brief, COMMON.md,
  dup-sweep.md (§0, §U13), README, the addendum (Part 1 and the *Lean parallelism* text), the phase-6 rulings,
  the handoff §2/§5, and the §1 inputs as they bear on U13.
- **Base check:** `git rev-parse bff0567b… bff0567b…^{tree}` gives `bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d`,
  `845bdc982fd8f79aba755796bb13188922c4655d` (as the brief). The 224 sources of `order.txt` match
  `SOURCE-SHA256SUMS` (`logs/source-sha256.log`).
- **Records tip at delivery** (`cryptography/pass-shelat-ch2-4`): `978fd46c18662882b5831b6b1c6049975d52086d`;
  `git merge-tree --write-tree 74fb355a… 978fd46c…` is clean, tree `77bdfc362021ddaacc5c77e5033c971bf69808b1`
  (information).

## 1. Environment (addendum Part 1; COMMON §3)

- **Preflight** (`logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the headroom is `MemAvailable` =
  16411054080 B = 15.28 GiB (floor 4 GiB); the clone's filesystem (ext4, `/dev/vda`) had 14796038144 B = 13.78 GiB
  free (floor 12 GiB): `PREFLIGHT PASS`. To get there, the worktree of this host's delivered `sc-ot` fill
  (`/workspace/scot`, branch kept) was removed; no dependency tree was copied or moved.
- **Clone:** a separate git worktree `/workspace/u13` of the local repository at B6, branch `fill/gsw-6b-u13`.
- **Cache:** the store (`~/.cache/mathlib`, `logs/cache-store.log`) held 2403 archives (120576651 B) from this host's
  earlier fills (not downloaded by this session). The narrowed `lake exe cache get` for the 102 roots of
  `roots.txt` (= the direct Mathlib imports of `order.txt`, checked) said "No files to download", decompressed 2339
  files and exited 0 (`logs/cache-get.log`); it cloned the manifest's packages, PFR included. No zero-size olean among
  2348 (`logs/zero-size-oleans.log`); the probe importing `Mathlib.Algebra.BigOperators.Field` elaborates
  (`logs/cache-probe.log`).
- **Packages** (`logs/packages-check.log`): `RESULT: all present packages match the manifest` (`doc-gen4`,
  `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT).
- **Pool** (`logs/pool.log`): `nproc` 4, `MemAvailable` 16.0 GB, so `min(nproc, MemAvailable/4 GB)` = 4; I ran
  **3**, the local-host cap, which satisfies either reading of this container (local host or cloud worker). No other
  job ran Lean on the machine. **One slip, disclosed:** at 21:56:18Z five two-second control probes were started at
  once (above 3) by a scripting error; everything else kept 3 (`pool_build.py` peak concurrency 3; seals by
  `xargs -P 3`). Peak max RSS of one Lean process: 2959360 KiB. No oom, no exit 137.
- **Bootstrap** (`logs/bootstrap.log`; `pool_build.py`, one `scripts/lean_check_tree.sh` call per module, in
  dependency order): 224/224 rc 0, 0 errors in both forms; `sorry` census = `base-sorries.txt` exactly (42
  declarations in 16 modules; `logs/census-bootstrap.txt`, `logs/census-bootstrap-vs-base.diff`).

## 2. The proofs (who wrote what: all by the lead)

The owned file `GSW/DecryptFormula.lean`: 216 lines at the base, 264 at the head (+55, −7; max width 98). Only the six
proof bodies and the module docstring's admission sentence changed (`All are statement-phase targets (admitted); the
definitions and the instance are proved.` → `All are proved, as are the definitions and the instance.`). **No sketch
was refreshed**: each frozen sketch already describes the delivered proof (the G8 proofs were written to follow
their sketches' `max_le` and `omega`).

- **G5** `vecMul_secretVector_eq_sum`. `ht : t = G·x` by `keyBits_eq` and `gadget_mulVec_decomposeVec`; then
  `dotProduct_comm`, `Matrix.dotProduct_mulVec`, `← decConstants_eq`, `dotProduct_comm`, and `rfl` (Mathlib's
  `dotProduct` is the stated sum).
- **G6** `decryptFormula_eval`. `decrypt_eq_decode_dotProduct` (the owner-side reader, as the brief requires; not
  re-derived), `decryptFormula_eq`, and `FormulaArith.modSumInterval_eval` with `aᵢ = (decConstants P C i).val`,
  `ZMod.val_lt`, and `decodeLo ≤ decodeHi ≤ q` (`decodeLo_eq`, `decodeHi_eq`, `P.lwe.modulus_ge_two`, `omega`).
  `hval`: the representative of `⟨t, c⟩` is `(∑ xᵢ·aᵢ.val) mod q` (G5, `Nat.cast_sum`, `Nat.cast_mul`,
  `ZMod.natCast_zmod_val`, `ZMod.val_natCast`). The two Booleans agree as propositions (`Bool.eq_iff_iff`,
  `decide_eq_true_iff`, `LWE.BitEncoding.decode_iff_mem_Ico`).
- **G7** `nandFormula_eval`. `nandFormula_eq`, `TreeCircuit.neg_eval`, `TreeCircuit.and2_eval`, G6 twice.
- **G8** `depth_nandFormula_le`. `FormulaArith.depth_modSumInterval_le` for both operands read back through
  `decryptFormula_eq` and `decDepth_eq`, `TreeCircuit.depth_and2_le`, `max_le`, `nandFormula_eq`,
  `TreeCircuit.depth_neg`, `omega`.
- **G8** `maxFanin_nandFormula_le`. `FormulaArith.maxFanin_modSumInterval_le` for both operands
  (`decryptFormula_eq`), `TreeCircuit.maxFanin_and2_le`, `nandFormula_eq`, `TreeCircuit.maxFanin_neg`, `omega`.
- **G8** `decDepth_le`. `⌈log₂ q⌉ ≤ ℓ` from `P.modulus_le` (`Nat.clog_le_iff_le_pow`); `Nat.clog_mono_right` on
  `⌈log₂ q⌉ + ⌈log₂ N⌉ + 3 ≤ ℓ + ⌈log₂ N⌉ + 3`; `FormulaArith.modSumDepth_le P.columns q`; `decDepth_eq`; `omega`.
  No term linear in `ℓ` enters (r3 §H3.3).

**Readers used** (census in `seals/reader-census.txt`, every foreign definition with its reader `path:line`;
MISSING: none): `decrypt_eq_decode_dotProduct` (`GSW/Scheme.lean:162`), `gadget_mulVec_decomposeVec`
(`GSW/Gadget.lean:164`), `LWE.BitEncoding.decode_iff_mem_Ico`, `decodeLo_eq`, `decodeHi_eq`
(`LWE/BitEncoding.lean:151,125,134`), `FormulaArith.modSumInterval_eval`, `depth_modSumInterval_le`,
`modSumDepth_le`, `maxFanin_modSumInterval_le` (`FormulaArith/ModSum.lean:193,303,365,380`),
`TreeCircuit.neg_eval`, `depth_neg`, `maxFanin_neg`, `and2_eval`, `depth_and2_le`, `maxFanin_and2_le`
(`FormulaArith/Combinators.lean:308,332,352,591,601,612`), the own readers `keyBits_eq`, `decConstants_eq`,
`decryptFormula_eq`, `nandFormula_eq`, `decDepth_eq`, and the fields `Parameters.modulus_le`,
`LWE.Parameters.modulus_ge_two`.

**Imports added:** none. **Helpers added:** none (so no helper docstrings).

## 3. Statement changes

None. (GSW unit: any change would be a blocker.)

## 4. Checks C1–C13 and the unit checks

- **C1 Bootstrap and sweep.** Bootstrap as §1. At the head: `DecryptFormula` (the only changed source) and its
  downstream, the 10 `UNIT-DOWN` rows of `closures.txt` (`logs/unit-down.txt`), rebuilt in order
  (`logs/head-sweep.log`): every rc 0, 0 errors. `build/summary.txt`: one row per module of `order.txt` (the head
  sweep's log for the 10, the bootstrap's for the other 214, whose sources are unchanged): rc, errors in both forms,
  `sorry` warnings, the SHA-256 of the source each check read, bound to `git show HEAD:<path>`: **224/224 rc 0, 0
  errors, bound**. The root `TCSlib` was not built.
- **C2 Admissions** (`admissions/`). Head census = `base-sorries.txt` minus U13's six targets: **36 declarations in
  15 modules** (`census-head.txt` against `expected-head.txt`: identical). No `sorry`, `admit`, `native_decide`,
  `axiom` or `opaque` token in the owned file.
- **C3 Statements** (`statements/`). The records' `decls2.py` (SHA-256 `fa81981a…`, as §1) on the owned file:
  **0 ADDED, 0 CHANGED, 0 REMOVED** (`decls2.txt` empty, `decls2.err` empty; `decls2-summary.txt` shows its parser
  saw the same 17 public declarations at base and head). `StmtDump` probes at the base (a verbatim copy of the base
  file, `base/DecryptFormulaBase.lean`) and at the head print the six targets and the eleven other public
  declarations with full names and types (`pp.fullNames`): **identical** (`stmtdump-diff.txt`). Targets → proofs:
  §2.
- **C4 Frozen check** (`frozen/`; `tools/lead/frozen_check_u13.py`, new, after the 6b statement delivery's
  `frozen_check6b.py`). Base vs head: 17/17 declarations either identical or (the six targets) with statement prose
  and header byte-identical; the one non-declaration change is the module docstring's admission sentence:
  **violations 0**. Controls, each with the stated count: 0 base vs itself → 0; 1 one-character header change → 1
  (HEADER); 2 an edit spilling from a sketch into statement prose → 1 (PROSE); 3 a definition's body → 1 (BODY,
  `decConstants`); 4 a reader → 1 (BODY, `decConstants_eq`); 5 an unpermitted import → 1 (TEXT); 6 a deleted target →
  1 (REMOVED); 7 an unlisted public declaration → 1 (ADDED). `git diff --stat bff0567b..HEAD` lists only the owned
  file.
- **C5 Axioms** (`axioms/`). `#print axioms` of the six targets: `[propext, Classical.choice, Quot.sound]` each.
  Census of every stored constant of the owned module (23: the 17 declarations and 6 auxiliary `_proof_` constants
  of `omega`): **0 with a non-standard axiom; the `sorryAx` dependency trace is empty**. Liveness control: the same
  census over the base copy finds 6 constants reaching `sorryAx`, each traced to itself (the six admitted targets)
  (`axioms-base-control.log`).
- **C6 Rule 10** (`seals/`). Whole-file seals (every TCSlib definition of the full import closure made irreducible
  and removed from instance unfolding; reducible abbreviations excluded as notation), compiled with
  `lean -DmaxErrors=0` on `lean_check_tree.sh`'s `LEAN_PATH`, in the four variants A/B × strict/coe (coe-A
  canonical), of the owned file at the head and of the base copy (recorded under the original path):
  **8/8 runs status 0, 0 errors; no failing declaration at the head** (`seals-summary.txt`, `runs/*.jsonl` and raw
  `runs/*.out`, sealed copies in `seals/sources/`). `PolyExpr` is not in this closure (`excluded=0` in the A
  variants), so A and B coincide; the one projection coercion of the closure is `FinDist.instCoeFunForallReal`
  (`coe-excluded=1`). **Paired controls** (`controls/`, unsealed `controls-plain.log`): `CtlUnfoldOwn`
  (`decConstants … := rfl`, the owner `DecryptFormula`) and `CtlUnfoldScheme` (`decrypt … := rfl`, the owner
  `GSW/Scheme.lean`) pass unsealed and **fail exactly once in each sealed variant**; `CtlReader` (the same facts by
  `decConstants_eq`, `decrypt_eq`) passes sealed; `CtlCoe` (the `FinDist` coercion by `rfl`) passes everywhere (a
  probe, not a negative control). No new public definition, so no further pair. Request sets: this method collects
  no request set (it seals the whole closure at the base's sources), so none can be stale (G6B-F11). **Explicit-unfold
  scan** (`scan/`): 27 identifiers given to `rw`/`simp`/… in the owned file at the head: 24 theorems, 3 local
  hypotheses, **0 definitions of any kind** (`scan-final.tsv`; base: 0 identifiers); `scan-compare.log`: "NEW foreign
  explicit unfolds: 0". Reader census: §2.
- **C7 Lint** (`lint/`). `style_lint.py` on the owned file: 0 findings at base and head.
  `campaign_style_lint.py TCSlib/Cryptography --check8b`: **92 FAIL / 103 WARN over 540 files** (rc 1) at base and
  head, as the maintainer's run; the FAIL/WARN line sets are identical (`campaign-lint-diff.txt`).
- **C8 Sizes** (`hygiene/sizes-hygiene.txt`). 216 lines (max width 98) → 264 (max width 98): 48 net fill lines,
  well under the brief's 200–330 estimate (the reuse list covered every step) and under its 550-line cap.
- **C9 Docstrings and sketches** (`hygiene/sizes-hygiene.txt`). No helper; every target keeps its sketch; the
  longest proof (G6, 20 lines) has its sketch and step comments at the major `have`s: **0 findings**.
- **C10 Clashes** (`clash/clash.txt`). No named declaration added (decls2, frozen check); the only new stored
  constants are six auxiliary `_proof_` constants under the targets' names, found nowhere at the base, on
  `iO/phase-a-base` `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` or on `cleanup/stage2-s2a`
  `dff281b53746377cd72e57c3aeeadf3d1f59a332` (heads read). No new short name, so no resolution in a `UNIT-DOWN` module
  can change.
- **C11 Reuse and overlap:** §5.
- **C12 Probe U13-P1** (`probes/ProbeU13P1.lean`, `logs/probe-u13-p1-final.log`; evidence only). `#eval` of
  `(decryptFormula P C).eval (keyBits P s)` against `decrypt P s C` at `n = 1`, `ℓ = 3`: `q = 5`, 15/15 pairs agree;
  `q = 8`, 24/24 agree (three ciphertexts `C i j = a·i + b·j + c`, every constant secret), and one pair printed
  `(false, false)`. A first run over 27 ciphertexts did not finish in 5 minutes and was stopped by its PID
  (`ProbeU13P1-v1.lean`, `probe-u13-p1.log`): the formula is a tree, and its evaluation is slow.
- **C13 Reproduction** (`logs/repro.log`). `git am` of `patches/` at the base in a scratch clone (`/tmp/u13-repro`,
  deleted afterwards) with the committer data of `COMMITS.tsv`: **every hash reproduced**; `src/` equals the head's
  file byte for byte. The commit is unsigned (`signing` column; `git cat-file -p HEAD | grep -c gpgsig` = 0).
- **Unit checks.** C2 count 36 in 15 ✓; C3 decls2 0/0/0 ✓; C12 U13-P1 ✓; no `sorryAx` (C5) ✓.

## 5. Overlap and reuse (C11)

**Searches** (`logs/dup-searches.log`, commands and hit counts; base, `iO/phase-a-base`, `cleanup/stage2-s2a`,
Mathlib/Batteries): the six target names (13 hits: their own file and docstrings of `GSW/Bootstrap.lean` citing them); the reused readers
(`gadget_mulVec_decomposeVec` 7, `decrypt_eq_decode_dotProduct` 5, `decode_iff_mem_Ico` 4, the F9/F10 lemmas 13, the
F1/F3 lemmas 64, `clog_le_iff_le_pow`/`clog_mono_right` 33, `ZMod.val_natCast`/`natCast_zmod_val` 76); shapes
`(∑ …).val` (5 hits, none a subset-sum representative lemma: `Encoding/DyadicLinearAlgebra.lean:207/409/423`,
`TrapdoorFunctions/AllButOne/AntiCyclic.lean:203/222`), `decodeLo … ≤ decodeHi` (0), `toNat * … .val` (8, unrelated);
Mathlib `val_sum`/`natCast_sum` (no ZMod-sum representative lemma), `dotProduct_mulVec`/`dotProduct_comm`,
`clog_le_iff_le_pow`/`clog_mono_right`.

**Must-reuse items of dup-sweep.md §U13**, with where they are used:

| Item | Used in |
|---|---|
| `gadget_mulVec_decomposeVec` (`GSW/Gadget.lean:164`) | G5 (`ht`) |
| `decrypt_eq_decode_dotProduct` (`GSW/Scheme.lean:162`) | G6 (not re-derived) |
| `secretVector_eq` (`Scheme.lean:71`) | not needed: `t` is read only through `gadget_mulVec_decomposeVec` |
| `vecMul_secretVector_augmented` (`:82`) | "only if needed": not needed |
| own readers `keyBits_eq`, `decConstants_eq`, `decryptFormula_eq`, `nandFormula_eq`, `decDepth_eq` | G5; G5; G6, G8 ×2; G7, G8 ×2; G8 depth, `decDepth_le` |
| `decode_iff_mem_Ico`, `decodeLo_eq`, `decodeHi_eq` (O2) | G6 |
| `modSumInterval_eval` | G6 |
| `depth_modSumInterval_le`, `maxFanin_modSumInterval_le` | G8 depth, G8 fan-in |
| `modSumDepth_le` | `decDepth_le` |
| `TreeCircuit.neg_eval`, `and2_eval` | G7 |
| `depth_neg`, `depth_and2_le`, `maxFanin_neg`, `maxFanin_and2_le` | G8 depth, G8 fan-in |
| Mathlib `Matrix.dotProduct_mulVec`, `dotProduct_comm` | G5 |
| `ZMod.val_natCast`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`, `Nat.cast_sum` | G6 (with `Nat.cast_mul`) |
| `Nat.clog_le_iff_le_pow`, `Nat.clog_mono_right` | `decDepth_le` |

**Near relatives and specializations (disclosed):**
- `decDepth_le` is `FormulaArith.modSumDepth_le` (`FormulaArith/ModSum.lean:365`) at `M = N`, weakened by
  `⌈log₂ q⌉ ≤ ℓ` (G6B-F05; ruled a target by Q-6B-F2 A). Its proof cites the lemma; nothing is re-proved.
- G6's local `hval` (the representative of the subset sum) is assembled from Mathlib lemmas; no TCSlib or Mathlib
  lemma states it (searches above). Its `hlh`/`hhq` (`decodeLo ≤ decodeHi ≤ q`) are one `omega` each from the two
  readers; no published lemma states them (0 hits).
- `TrapdoorFunctions/Lossy.gadget`'s bit-decomposition lemmas: not used (G5 is over `decomposeVec`; the GSW reader
  `gadget_mulVec_decomposeVec` is the one cited).
- No exact restatement, no inline re-derivation of a published lemma, no private or cross-file copy.

## 6. Promotion requests

None.

## 7. Scope requests

None. No frozen file was touched; no reader was missing.

## 8. Checkpoints

- **Checkpoint 1** (exchange commit `ab9d1ec3a`): head `74fb355a…`, all six targets proved, C1–C13 run (a full
  payload, as COMMON §8 requires; the brief asked for G5, G7, G8).
- **Final** (this delivery): the same head and evidence, with this report as the final one. The records tip was
  re-read at delivery (unchanged, `978fd46c…`; merge-tree tree unchanged).

## 9. Probes and attribution

No citation was added or changed (no docstring outside the admission sentence changed). Probes are under `probes/`
and outside the library (`lean_proof/u13/…` in the worktree).

## 10. Questions for Seyoon

- **U13-W1 · the folder's `rulings.md` is missing at the records pin.** The dispatch prompt names
  `briefs/lattice-gsw/phase6/issued-6b-fills-r1/rulings.md` as the first input, but the pin `bbc930b3…` (and the
  records tip `978fd46c…`) has no such file, and the README's *Maintainer steps* say it is filed with the folder's
  final form. **A** (recommended): confirm that U13 needs no ruling (the README says U12 and U13 depend on none of
  Q-6BF-1 to Q-6BF-7) and accept this delivery as is; record the omission in the decision log · **B** file
  `rulings.md` and have this delivery re-checked against it.

## 11. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

- `logs/`: `inputs-check.log`, `preflight.log`, `source-sha256.log`, `order.txt`, `mathlib-roots.txt`,
  `cache-store.log`, `cache-get.log`, `packages-check.log`, `zero-size-oleans.log`, `cache-probe.log`, `pool.log`,
  `bootstrap.log`, `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`, `unit-down.txt`, `head-sweep.log`,
  `base-copy.log`, `dup-searches.log`, `probe-u13-p1.log`, `probe-u13-p1-one.log`, `probe-u13-p1-final.log`,
  `repro.log`.
- `build/summary.txt`; `admissions/` (head census, expected rows, check); `statements/` (decls2 output and summary,
  `StmtDump` logs and diff); `frozen/` (head check and the eight controls); `axioms/` (head census, base control);
  `seals/` (`seals-summary.txt`, `runs/`, `sources/`, `controls-plain.log`, `reader-census.txt`); `controls/`;
  `base/DecryptFormulaBase.lean`; `scan/` (ids, raw logs, tsv, compare, sources); `lint/`; `hygiene/`; `clash/`;
  `probes/` (`CacheProbe`, `StmtDumpBase`, `StmtDumpHead`, `AxiomsU13`, `AxiomsU13Base`, `ProbeU13P1`,
  `ProbeU13P1-one`, `ProbeU13P1-v1`).
- `tools/`: every script used (`check.sh`, `pool_build.py`, `census.py`, `pkgcheck.py`, `seal_gen.py`,
  `seal_run.py`, `seal_jobs.sh`, `rwids.py`, `rwids_run.sh`, `cmp_scans.py`, `width_check.py`, `payload.sh`,
  `repro_check.sh`, `manifest.sh`, `lead/decls2_summary.py`, `lead/frozen_check_u13.py`, `lead/sizes_hygiene.py`,
  `lead/summary.py`, `records/decls2.py` — the records' copy, unchanged).
- `patches/` (one patch and `COMMITS.tsv` with the signing column), `src/` (the owned file at the head).

The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/gsw-6b-u13/` except itself, without a leading
`./`; its paths equal the delivered files (checked before the push).
