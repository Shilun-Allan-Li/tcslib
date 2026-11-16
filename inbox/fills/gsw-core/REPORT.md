# Fill `gsw-core` — checkpoint 1 (F1 Gadget, F2 Noise; F4 Eval proved modulo F3)

**Worker** Claude, lead with two sub-agents (A, B). **Issue base**
`486f44f8414c20a2d21e452c44de8b8c8d8513a0` (head of draft PR #333, `stmt/gsw`), verified to contain
#332's `94eae71b779c4ca0f76c138d699f4d737dbd6cee` (`git merge-base --is-ancestor`). Pack read at
exchange commit `523d4e97302606b0301ecbcff13882abb917ec1f`; `shasum -a 256 -c SHA256SUMS` in
`outbox/fills/gsw-core/`: all 7 files OK. Local branch `fill/gsw-core` (never pushed), head at this
checkpoint `a1bc6aacd11f227c7f1e4a82475ec936380b3cd9`. Lean 4.25.0; Mathlib and packages at the
base's `lake-manifest.json`.

## Status of the 29 targets

| Unit | File | Target | Status at checkpoint 1 | Prover |
|---|---|---|---|---|
| F1 | Gadget | `digits_decomposeVec`, `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`, `decomposeVec_block_eq_false`, `errorSum_decomposeVec_le` | **proved** (standard axioms) | sub-agent A |
| F2 | Noise | `encrypts_gadget`, `encrypts_zero`, `Encrypts.mono`, `.add`, `.neg`, `.sub`, `.sum`, `.mul`, `.mul_bit`, `.mul_le`, `.nand`, `encrypts_chain` | **proved** (standard axioms) | sub-agent A |
| F4 | Eval | `homAnd_encrypts`, `homGate_encrypts`, `eval_encrypts` | **proved** (standard axioms) | lead |
| F4 | Eval | `decrypt_keygen_eval` | proved, **modulo F3**: reaches `sorryAx` only through the cited frozen F3 targets `encrypts_keygen_encrypt` and `decrypt_of_encrypts` | lead |
| F3 | Scheme | 6 targets | open (sub-agent B working) | — |
| F7 | Symmetric | 2 targets | open (sub-agent B working) | — |

This checkpoint removes **21** admissions: the 5 F1, 12 F2 and 4 F4 targets (list in
`evidence/sorries/cp1.txt`). 14 of the base's 35 remain: 6 Scheme, 2 Symmetric (this job), and the
6 of `gsw-security` (`Hashing/SIS/Columns` 2, `GSW/Security` 4). Nothing was added.

## Commits (`patches/`, `patches/COMMITS.tsv`)

1. `243a44cdb` — F1, F2 (Gadget.lean, Noise.lean; sub-agent A's files, integrated by the lead).
2. `a1bc6aacd` — F4 (Eval.lean; lead).

All commits made with `git -c commit.gpgsign=false`; none is signed (`signing` column `none`).
Reproduction: a scratch clone at the base applies the series with `git am` under the recorded
committer identity and date and reproduces both hashes, and the reproduced files equal `src/`
(`evidence/logs/patch-reproduction.log`).

## Changed files (lines at base → checkpoint)

| File | Lines | Changes |
|---|---|---|
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Gadget.lean` | 204 → 236 | 5 bodies; sketches of `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`, `decomposeVec_block_eq_false` (last sentence), `errorSum_decomposeVec_le` rewritten to the delivered proofs |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Noise.lean` | 235 → 321 | 12 bodies; sketches of `encrypts_gadget`, `encrypts_zero`, `.add`, `.neg`, `.mul`, `.mul_bit`, `.mul_le`, `.nand`, `encrypts_chain` rewritten |
| `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Eval.lean` | 209 → 321 | 4 bodies; sketch of `homGate_encrypts` rewritten (the other three already describe the delivered proofs) |

No statement prose, header, definition, reader, `variable`/`section`/`open`/`set_option` line,
import or module docstring changed (`evidence/headers/cp1/headers.txt`). No frozen file is touched.

## New declarations

None. No auxiliary lemma, definition, attribute or import was added.

## Routes (as delivered)

- **F1/F2** follow the brief. `Encrypts.mul` keeps the exact `x₁.natAbs * β₂` term: witness
  `j ↦ (∑ᵢ e₁ i · X i j) + x₁ · e₂ j`, `Matrix.vecMul_vecMul`, `Matrix.add_vecMul`,
  `Matrix.smul_vecMul`, `gadget_mul_decompose`, `LWE.binaryErrorSum_bound`, `Int.natAbs_mul`.
  `errorSum_decomposeVec_le` reindexes through `finProdFinEquiv`, kills the off-blocks with
  `decomposeVec_block_eq_false` and applies `LWE.binaryErrorSum_bound` with `m := ℓ`.
- **F4.** `homAnd_encrypts`: induction on the `Forall₂`, splitting the tail into `[]`/`_ :: _` to
  follow `homAnd`'s three equations, `Encrypts.mul_bit` with the head on the left.
  `homGate_encrypts`: `List.forall₂_map_left_iff`/`_right_iff`/`List.forall₂_same`, `List.all_map`,
  the length bound, then `¬` = `G − ·`, `∨` = De Morgan (`List.any_eq_not_all_not`).
  `eval_encrypts`: `runWith_rel` with `R v b C := Encrypts P t b.toNat ((N+1)^{Cc.depthAt v}·β) C`,
  `depthAt_input`, `depthAt_gate`, `depthAt_eq`, `DAGGate.depth_eq`, `DAGGate.getD_lt_depth`,
  `Encrypts.mono`/`Nat.pow_le_pow_right`, `homGate_encrypts`; output read with `Cc.eval_eq`,
  `values_eq`, `depth_eq`, `eval_eq`, `evalValues_eq`. Full `IsFaninTwo` not used; no reader added.
  `decrypt_keygen_eval`: `encrypts_keygen_encrypt`, `eval_encrypts`, `.mono` with
  `Nat.pow_le_pow_right` and `hdepth`, `decrypt_of_encrypts` with the declared `hsep` verbatim.

## Overlap and reuse

No new declarations. Inline re-proofs and specializations:

1. **`Encrypts.mul`, inline `hX`** (`e₁ᵗ · lift X` is the residue of the integer binary sum).
   Nearest relatives: the inline `herr` of `Regev.encrypt_residual`
   (`TCSlib/Cryptography/Encryption/PublicKey/Regev/Basic.lean:119`) and the last step of
   `Lossy.residual_conceal` (`TCSlib/Cryptography/TrapdoorFunctions/Lossy/Matrix.lean:128`). Same
   cast step (`Int.cast_sum`/`Int.cast_mul`/`Int.cast_natCast`); both are inline in other proofs,
   not stated lemmas; three lines of glue.
2. **Bool-message identities** `((a && c).toNat : ℤ) = a.toNat * c.toNat` and
   `((!c).toNat : ℤ) = 1 − c.toNat`, proved inline by `cases … <;> rfl` in `Encrypts.mul_le`,
   `Encrypts.nand`, `encrypts_chain` (Noise) and `homAnd_encrypts`, `homGate_encrypts` (Eval). No
   core or Mathlib lemma at the pin states them over `ℤ` (searched core `Init/Data/Bool.lean`,
   `Mathlib/Data/Bool/*`, batteries for `toNat_and|toNat_not|toNat_mul`). Noise and Eval are
   different files, and a shared public lemma would change Noise's interface; kept inline.
3. **`homGate_encrypts`, inline `hlen`** (`((k−1)·N+1)·β ≤ (N+1)·β` for `k ≤ 2`): arithmetic glue,
   no relative.
4. **Reused, not re-proved:** `LWE.binaryErrorSum_bound` (`TCSlib/Cryptography/LWE/Basic.lean:79`;
   not its specializations `Regev.subsetError_bound`, `Lossy.error_sum_bound`),
   `Lossy.gadget_mulVec` (`Lossy/Gadget.lean:214`), `Lossy.digits_val` (`:183`), `Lossy.digits_eq`,
   `runWith_rel`, `DAGGate.getD_lt_depth`, `depthAt_input`, `depthAt_gate` (`DAGCircuit.lean`), and
   Mathlib's `List.getD_eq_getElem`/`List.getElem_ofFn` for `getD` of `List.ofFn` (no copy of the
   DL-47 family).

Searches: `grep -rn` over `TCSlib/` for `Int.cast_sum`, `error_sum_bound|subsetError_bound`,
`toNat` (GSW files), `runWith_rel|runWith_sim|runWith_remap_rel`, `getD_eq_getElem|getElem_ofFn`;
Mathlib/core/batteries for the Bool identities; `#check` probes (`evidence/lead/probes/LeadNames.lean`,
`evidence/subagents/A/probes/NamesA.lean`) for every Mathlib name used.

## Scope requests and promotion requests

None.

## Who proved what

- **Sub-agent A** (worktree `/home/user/gsw-A`, own olean tree): F1 and F2, all 17 targets. Its
  report, worklog, logs, probes and seals are in `evidence/subagents/A/` (the harness refused a
  sub-agent-written `.md` report, so the lead saved its returned report as `REPORT.md` there).
- **Sub-agent B** (worktree `/home/user/gsw-B`): F3 and F7, in progress. Its evidence folder is
  still being written and is **not part of this checkpoint**; it is delivered with the next one.
- **Lead**: F4 (4 targets), integration, every commit, all checks and the delivery.

All Lean runs (lead and sub-agents) were serialized by one `flock` on `/home/user/gsw/.lean.lock`
(`evidence/tools/runlean.py`, `chk.sh`, `seal.py`); no `lake build`, no unfiltered cache fetch.

## Environment (addendum Part 1)

- Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1, limit 14,338,772,992 B, memory in
  use (usage − total_cache + total_shmem) 470,822,912 B, **headroom 12.92 GiB**; clone filesystem
  ext4 on `/dev/vda`, **15.65 GiB free**; no tmpfs. Re-check before the cache fetch: 13.2 GiB free.
- Toolchain `leanprover/lean4:v4.25.0` installed by elan after the preflight.
- Cache store (`evidence/logs/cache-store.log`): `/root/.cache/mathlib` absent before the fetch
  (0 archives pre-existing). Narrowed fetch for the **38** roots of `roots.txt` (recomputed from
  `order.txt`, identical: `evidence/logs/mathlib-roots.txt`): "Attempting to download 2060",
  "Decompressing 2060", completed successfully (`evidence/logs/cache-get.log`).
- Packages check (`evidence/logs/packages-check.log`): last line "RESULT: PASS: present packages
  match the manifest; absent: «doc-gen4», UnicodeBasic, BibtexQuery, MD4Lean". Zero-size oleans: 0.
  Root probe `import Mathlib.Algebra.BigOperators.Field` elaborated (`evidence/logs/cache-probe.log`).
- Bootstrap: all 31 modules of `order.txt`, in order, 0 errors (`evidence/logs/bootstrap.log`,
  per-module logs with start/end time and peak RSS in `evidence/logs/bootstrap/`).
  `/usr/bin/time` is absent on this host; peak RSS is recorded by `runlean.py` (`getrusage`).
- Sub-agent worktrees have their own TCSlib olean trees (copied from the lead's bootstrapped
  TCSlib tree) and `.lake/packages` symlinked to the lead's; only the lead ran `lake`.
- A detached base worktree `/home/user/gsw-base` (own TCSlib olean tree, Eval and facades re-checked
  at the base) runs the base seals and the base lint.

## Checks at this checkpoint (`evidence/`)

| Check | Result | Evidence |
|---|---|---|
| Owned modules | 5/5 exit 0, 0 errors (both forms), sorry warnings Gadget 0, Noise 0, Eval 0, Scheme 6, Symmetric 2 | `logs/cp1/modules/`, `logs/cp1/modules.txt` |
| Sweep of `order.txt` | 31/31, 0 errors | `logs/cp1/sweep/`, `logs/cp1/sweep.txt` |
| Admissions | 35 → 14; removed exactly the 21 listed; added 0 | `sorries/cp1.txt` |
| Axioms + dependency trace | 108 stored constants; all F1, F2 targets and `homAnd_encrypts`, `homGate_encrypts`, `eval_encrypts`: `propext`, `Classical.choice`, `Quot.sound` only; 9 constants reach `sorryAx`: the 8 open F3/F7 targets (each only itself) and `decrypt_keygen_eval` (only via `decrypt_of_encrypts`, `encrypts_keygen_encrypt`) | `axioms/cp1/` |
| Frozen statements | 0 unexpected differences; controls PASS in all 5 files (1-char header change → exactly 1 difference; deleted reader → exactly 1 removal) | `headers/cp1/` |
| Width / size | max width ≤ 100, files ≤ 1000 lines, no `µ` | `width/cp1.txt` |
| Name clash | 0 (no new names) | `clash/cp1.txt` |
| Explicit-unfold scan (Lean-resolved, TCSlib **and** core/Mathlib definitions) | 0 flagged | `unfold/cp1/` |
| Seals, base (5 files × A/B × strict/coe, `-DmaxErrors=0`) | 20/20 exit 0, 0 errors, harness valid | `seals/base/` |
| Seals, checkpoint (Gadget, Noise, Eval × 4) | 12/12 exit 0, 0 errors, harness valid; **coe-A canonical: 0 failing declarations**; strict = coe + 1 request (FinDist's projection coercion), no difference in errors | `seals/cp1/` |
| Paired controls | unsealed 0 errors; 6 POS pass sealed; 8 NEG fail exactly once in each of the 4 variants (`gadget`, `mul`, `Encrypts`, `Regev.augmented`, `LWE.sample`, `Lossy.gadget`, `Randomized.blocksEquiv`, `BitEncoding.codepoint`); COE passes coe, fails once strict; **ALL_OK** | `seals/controls-cp1/` |
| Lint `--check8b` | base 92 FAIL / 101 WARN / 364 files; checkpoint identical line sets (0 new, 0 removed) | `lint/` |

Notes on the seals. Seal A and seal B install the same set here: `Complexity.PolyExpr` is outside
the import closure of every owned file (and of the control probe), so there is no `PolyExpr.eval`
control. Error counts use `^\S+\.lean:\d+:\d+: error[:(]` on every raw log (seals, controls, sweep,
probes). The seal harness (`evidence/tools/seal.py`, `seal_install.lean.txt`) copies verbatim the
install block of the derand fill's harness (exchange `inbox/fills/derand/evidence/verification/
tools/make_seals.py`, after Gate 10's), only renaming its log prefix.

Tool corrections during this checkpoint (disclosed): the first `ctlcheck.py` run keyed controls by
name only, so each POS/NEG pair sharing a name was miscounted; and the first `axioms_report.py`
missed the summary line. Both tools were fixed and re-run on the same raw logs; the first outputs
are retained in `logs/cp1/evidence-run.out`.

## Evidence manifest

`evidence/SHA256SUMS` lists every evidence file; the top-level `SHA256SUMS` lists every delivered
file under `inbox/fills/gsw-core/` except itself; the delivered paths equal the manifest's exactly.
